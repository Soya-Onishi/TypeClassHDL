package tchdl.typecheck

import tchdl.ast._
import tchdl.util._

import scala.reflect.classTag
import scala.reflect.runtime.universe.typeTag

object BuildImplContainer {
  type TopLevelDefinition = {
    val hp: Vector[ValDef]
    val tp: Vector[TypeDef]
    val bounds: Vector[BoundTree]
    def symbol: Symbol
  }

  def exec(cu: CompilationUnit)(implicit global: GlobalData): Unit = {
    val packageSymbol = cu.pkgName.foldLeft[Symbol.PackageSymbol](global.rootPackage) {
      case (pkg, name) =>
        val Right(child) = pkg.lookup[Symbol.PackageSymbol](name).toEither
        child
    }

    val ctx = packageSymbol.lookupCtx(cu.filename).get

    cu.topDefs.foreach(buildContainer(_)(ctx, global))
  }

  def buildBounds(bound: BoundTree)(implicit ctx: Context.NodeContext, global: GlobalData): Either[Error, Bound] = {
    def buildTPBounds(bound: TPBoundTree): Either[Error, TPBound] = {
      val (targetErrs, target) = TPBound.buildTarget(bound.target)
      val (boundsErrs, bounds) = TPBound.buildBounds(bound.bounds)

      val errs = Vector(targetErrs, boundsErrs).flatten
      if (errs.nonEmpty) Left(Error.MultipleErrors(errs: _*))
      else Right(TPBound(TPBoundTree(target, bounds, Position.empty)))
    }

    def buildHPBounds(bound: HPBoundTree): Either[Error, HPBound] = {
      val hpBound = HPBound.build(bound)
      val typedTarget = HPBound.typed(hpBound.target)
      val typedBounds = hpBound.bound match {
        case HPConstraint.Range(max, min) =>
          val (maxErr, maxExpr) = max.map(HPBound.typed).partitionMap(identity)
          val (minErr, minExpr) = min.map(HPBound.typed).partitionMap(identity)
          val errs = maxErr ++ minErr

          if (errs.nonEmpty) Left(Error.MultipleErrors(errs: _*))
          else Right(HPConstraint.Range(maxExpr, minExpr))
        case HPConstraint.Eqn(exprs) =>
          val (errs, eqns) = exprs.map(HPBound.typed).partitionMap(identity)
          if (errs.isEmpty) Right(HPConstraint.Eqn(eqns))
          else Left(Error.MultipleErrors(errs: _*))
      }

      (typedTarget, typedBounds) match {
        case (Left(targetErr), Left(boundsErr)) => Left(Error.MultipleErrors(targetErr, boundsErr))
        case (Left(err), _) => Left(err)
        case (_, Left(err)) => Left(err)
        case (Right(t), Right(bs)) => Right(HPBound(t, bs))
      }
    }

    bound match {
      case bound: TPBoundTree => buildTPBounds(bound)
      case bound: HPBoundTree => buildHPBounds(bound)
    }
  }

  def setBoundsForTopDefinition(definition: TopLevelDefinition)(implicit ctx: Context.RootContext, global: GlobalData): Unit = {
    definition.symbol.tpe // run Namer for hardwareParam, typeParam and components

    val signatureCtx = Context(ctx, definition.symbol)
    signatureCtx.reAppend(
      definition.hp.map(_.symbol) ++
        definition.tp.map(_.symbol): _*
    )

    val (builtErrs, bounds) = definition.bounds
      .map(buildBounds(_)(signatureCtx, global))
      .partitionMap(identity)

    val verifyErrs = HPBound.verifyForm(bounds.collect { case bound: HPBound => bound }) match {
      case Right(()) => Vector.empty
      case Left(err) => Vector(err)
    }

    val errs = builtErrs ++ verifyErrs

    errs match {
      case Vector() => definition.symbol.asTypeSymbol.setBound(bounds)
      case errs => errs.foreach(global.repo.error.append)
    }
  }

  def implementInterface(impl: ImplementInterface)(implicit ctx: Context.RootContext, global: GlobalData): Unit = {
    def verifyTypeValidity(interface: Type.RefType, target: Type.RefType, ctx: Context.NodeContext): Either[Error, Unit] =
      (interface.origin.flag, target.origin) match {
        case (flag, _: Symbol.ModuleSymbol) if flag.hasFlag(Modifier.Interface) => Right(())
        case (flag, _: Symbol.StructSymbol) if flag.hasFlag(Modifier.Trait) => Right(())
        case (flag, _: Symbol.EnumSymbol) if flag.hasFlag(Modifier.Trait) => Right(())
        case (_, _: Symbol.ModuleSymbol) => Left(Error.TryImplTraitByModule(impl))
        case (_, _: Symbol.StructSymbol) => Left(Error.TryImplInterfaceByStruct(impl))
        case (_, _: Symbol.EnumSymbol) => Left(Error.TryImplInterfaceByStruct(impl))
        case (flag, tp: Symbol.TypeParamSymbol) =>
          val bounds = ctx.tpBounds.find(_.target.origin == tp).map(_.bounds).getOrElse(Vector.empty)

          val hasConsistency = bounds match {
            case Vector() => true
            case bounds if bounds.head.origin.flag.hasFlag(Modifier.Interface) =>
              bounds.forall(_.origin.flag.hasFlag(Modifier.Interface))
            case bounds if bounds.head.origin.flag.hasFlag(Modifier.Trait) =>
              bounds.forall(_.origin.flag.hasFlag(Modifier.Trait))
          }

          val isInterfaceBounds = bounds.forall(_.origin.flag.hasFlag(Modifier.Interface)) && bounds.nonEmpty
          val isTraitBounds = bounds.forall(_.origin.flag.hasFlag(Modifier.Trait)) && bounds.nonEmpty

          if (!hasConsistency) Left(Error.TypeParameterMustHasConsistency(bounds))
          else {
            if (isInterfaceBounds && flag.hasFlag(Modifier.Trait)) Left(Error.TryImplTraitByModule(impl))
            else if (isTraitBounds && flag.hasFlag(Modifier.Interface)) Left(Error.TryImplInterfaceByStruct(impl))
            else Right(())
          }
      }

    val signatureCtx: Context.NodeContext = Context(ctx, impl.symbol)
    val implSymbol = impl.symbol.asImplementSymbol

    signatureCtx.reAppend(implSymbol.hps ++ implSymbol.tps: _*)

    val (interfaceErr, interface) = Type.buildType[Symbol.InterfaceSymbol](impl.interface)(
      signatureCtx,
      global,
      classTag[Symbol.InterfaceSymbol],
      typeTag[Symbol.InterfaceSymbol]
    )

    val (targetErr, target) = Type.buildType[Symbol.TypeSymbol](impl.target)(
      signatureCtx,
      global,
      classTag[Symbol.TypeSymbol],
      typeTag[Symbol.TypeSymbol]
    )

    val signatureErr = Vector(interfaceErr, targetErr).flatten
    val (buildErrs, bounds) = impl.bounds
      .map(buildBounds(_)(signatureCtx, global))
      .partitionMap(identity)

    val verifyErrs = HPBound.verifyForm(bounds.collect { case bound: HPBound => bound }) match {
      case Right(()) => Vector.empty
      case Left(err) => Vector(err)
    }

    val errs = signatureErr ++ buildErrs ++ verifyErrs
    val result =
      if (errs.isEmpty) Right(bounds)
      else Left(Error.MultipleErrors(errs: _*))

    result match {
      case Right(bounds) => verifyTypeValidity(interface.tpe.asRefType, target.tpe.asRefType, signatureCtx) match {
        case Left(err) => global.repo.error.append(err)
        case Right(_) =>
          val implContext = Context(signatureCtx, target.tpe.asRefType)
          impl.methods.foreach(Namer.nodeLevelNamed(_)(implContext, global))
          impl.types.foreach(Namer.nodeLevelNamed(_)(implContext, global))

          val interfaceTpe = interface.tpe.asRefType
          val targetTpe = target.tpe.asRefType
          impl.interface.setTpe(interfaceTpe).setSymbol(interface.symbol)
          impl.target.setTpe(targetTpe).setSymbol(target.symbol)

          val container = ImplementInterfaceContainer(impl, ctx, interfaceTpe, targetTpe, implContext.scope)

          val interfaceSymbol = interface.symbol.asInterfaceSymbol
          impl.symbol.asImplementSymbol.setBound(bounds)
          interfaceSymbol.appendImpl(impl, container)
          global.buffer.traits.append(interfaceSymbol)
      }
      case Left(err) => global.repo.error.append(err)
    }
  }

  def implementClass(impl: ImplementClass)(implicit ctx: Context.RootContext, global: GlobalData): Unit = {
    val signatureCtx = Context(ctx, impl.symbol)
    val implSymbol = impl.symbol.asImplementSymbol
    signatureCtx.reAppend(implSymbol.hps ++ implSymbol.tps: _*)

    val (signatureErr, target) = Type.buildType[Symbol.ClassTypeSymbol](impl.target)(
      signatureCtx,
      global,
      classTag[Symbol.ClassTypeSymbol],
      typeTag[Symbol.ClassTypeSymbol],
    )

    val (boundErrs, bounds) = impl.bounds
      .map(buildBounds(_)(signatureCtx, global))
      .partitionMap(identity)

    val verifyErrs = HPBound.verifyForm(bounds.collect { case bound: HPBound => bound }) match {
      case Right(()) => Vector.empty
      case Left(err) => Vector(err)
    }

    val errs = boundErrs ++ verifyErrs ++ signatureErr.toVector

    errs match {
      case Vector() =>
        val implContext = Context(signatureCtx, target.tpe.asRefType)
        impl.components.foreach(Namer.nodeLevelNamed(_)(implContext, global))

        val targetTpe = target.tpe.asRefType
        impl.target.setTpe(targetTpe).setSymbol(target.symbol)

        val container = ImplementClassContainer(impl, ctx, targetTpe, implContext.scope)

        val targetSymbol = target.symbol.asClassTypeSymbol
        val implSymbol = impl.symbol.asImplementSymbol
        implSymbol.setBound(bounds)
        targetSymbol.appendImpl(impl, container)
        global.buffer.clazz.append(targetSymbol)
      case errs =>
        errs.foreach(global.repo.error.append)
    }
  }

  def buildContainer(defTree: Definition)(implicit ctx: Context.RootContext, global: GlobalData): Unit =
    defTree match {
      case module: ModuleDef => setBoundsForTopDefinition(module)
      case struct: StructDef => setBoundsForTopDefinition(struct)
      case interface: InterfaceDef => setBoundsForTopDefinition(interface)
      case enum: EnumDef => setBoundsForTopDefinition(enum)
      case impl: ImplementInterface => implementInterface(impl)
      case impl: ImplementClass => implementClass(impl)
      case _ =>
    }
}
