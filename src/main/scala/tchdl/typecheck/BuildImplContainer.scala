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

    val ctx = packageSymbol.lookupCtx(cu.filename.get).get

    cu.topDefs.foreach(buildContainer(_)(ctx, global))
  }

  def buildBounds(bound: BoundTree)(implicit ctx: Context.NodeContext, global: GlobalData): Either[Error, Bound] = {
    def buildTPBounds(bound: TPBoundTree): Either[Error, TPBound] = {
      val (targetErrs, target) = TPBound.buildTarget(bound.target)
      val (boundsErrs, bounds) = TPBound.buildBounds(bound.bounds)

      val errs = Vector(targetErrs, boundsErrs).flatten
      if(errs.nonEmpty) Left(Error.MultipleErrors(errs: _*))
      else Right(TPBound(TPBoundTree(target, bounds)))
    }

    def buildHPBounds(bound: HPBoundTree): Either[Error, HPBound] = {
      def build(expr: HPExpr): Either[Error, HPExpr] = expr match {
        case HPBinOp(op, left, right) => (build(left), build(right)) match {
          case (Right(l), Right(r)) => Right(HPBinOp(op, l, r).setTpe(Type.numTpe).setID(expr.id))
          case (Left(err0), Left(err1)) => Left(Error.MultipleErrors(err0, err1))
          case (Left(err), _) => Left(err)
          case (_, Left(err)) => Left(err)
        }
        case ident @ Ident(name) => ctx.lookup[Symbol.HardwareParamSymbol](name) match {
          case LookupResult.LookupSuccess(symbol) => symbol.tpe match {
            case Type.ErrorType => Right(ident.setSymbol(Symbol.ErrorSymbol).setTpe(Type.ErrorType))
            case tpe: Type.RefType =>
              if(tpe == Type.numTpe) Right(ident.setSymbol(symbol).setTpe(Type.numTpe))
              else Left(Error.RequireNumTerm(ident, tpe))
          }
          case LookupResult.LookupFailure(err) =>
            ident.setSymbol(Symbol.ErrorSymbol).setTpe(Type.ErrorType)
            Left(err)
        }
        case lit: IntLiteral => Right(lit.setTpe(Type.numTpe))
        case lit: StringLiteral =>  Left(Error.RequireNumTerm(lit, Type.strTpe))
      }

      HPBound.verifyForm(bound) match {
        case Left(err) => Left(err)
        case Right(_) =>
          val hpBound = HPBound(bound)
          val target = build(hpBound.target)
          val bounds = hpBound.bound match {
            case HPRange.Range(eRange, cRange) =>
              val (maxErr, max) = eRange.max.map(build).partitionMap(identity)
              val (minErr, min) = eRange.min.map(build).partitionMap(identity)
              val (neErr, ne) = eRange.ne.map(build).partitionMap(identity)
              val errs = maxErr ++ minErr ++ neErr

              if(errs.nonEmpty) Left(Error.MultipleErrors(errs: _*))
              else Right(HPRange.Range(HPRange.ExprRange(max, min, ne), cRange))
            case HPRange.Eq(range: HPRange.ExprEqual) => build(range.expr) match {
              case Right(expr) => Right(HPRange.Eq(HPRange.ExprEqual(expr)))
              case Left(err) => Left(err)
            }
            case range @ HPRange.Eq(_: HPRange.ConstantEqual) => Right(range)
          }

          (target, bounds) match {
            case (Right(t), Right(bs)) => Right(HPBound(t, bs))
            case (Left(targetErr), Left(boundsErr)) => Left(Error.MultipleErrors(targetErr, boundsErr))
            case (Left(err), _) => Left(err)
            case (_, Left(err)) => Left(err)
          }
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
      definition.tp.map(_.symbol) : _*
    )

    val (errs, bounds) = definition.bounds
      .map(buildBounds(_)(signatureCtx, global))
      .partitionMap(identity)

    errs match {
      case Vector() => definition.symbol.asTypeSymbol.setBound(bounds)
      case errs => errs.foreach(global.repo.error.append)
    }
  }

  def implementInterface(impl: ImplementInterface)(implicit ctx: Context.RootContext, global: GlobalData): Unit = {
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
    val (errs, bounds) = impl.bounds
      .map(buildBounds(_)(signatureCtx, global))
      .partitionMap(identity)

    (errs ++ signatureErr) match {
      case Vector() =>
        val implContext = Context(signatureCtx, target.tpe.asRefType)
        impl.methods.foreach(Namer.nodeLevelNamed(_)(implContext, global))

        val interfaceTpe = interface.tpe.asRefType
        val targetTpe = target.tpe.asRefType
        impl.interface.setTpe(interfaceTpe).setSymbol(interface.symbol)
        impl.target.setTpe(targetTpe).setSymbol(target.symbol)

        val container = ImplementInterfaceContainer(impl, ctx, interfaceTpe, targetTpe, implContext.scope)

        val interfaceSymbol = interface.symbol.asInterfaceSymbol
        impl.symbol.asImplementSymbol.setBound(bounds)
        interfaceSymbol.appendImpl(impl, container)
        global.buffer.interface.append(interfaceSymbol)
      case errs =>
        errs.foreach(global.repo.error.append)
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

    val errs = boundErrs ++ signatureErr.toVector

    errs match {
      case Vector() =>
        val implContext = Context(signatureCtx, target.tpe.asRefType)
        impl.methods.foreach(Namer.nodeLevelNamed(_)(implContext, global))
        impl.stages.foreach(Namer.nodeLevelNamed(_)(implContext, global))

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
      case impl: ImplementInterface => implementInterface(impl)
      case impl: ImplementClass => implementClass(impl)
      case _ =>
    }
}
