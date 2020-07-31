package tchdl.typecheck

import tchdl.util.TchdlException._
import tchdl.util._
import tchdl.ast._

object TopDefTyper {
  def exec(cu: CompilationUnit)(implicit global: GlobalData): CompilationUnit = {
    val ctx = global.rootPackage.search(cu.pkgName)
      .getOrElse(throw new ImplementationErrorException(s"${cu.pkgName} should be there"))
      .lookupCtx(cu.filename)
      .getOrElse(throw new ImplementationErrorException(s"${cu.filename}'s context should be there'"))

    val topDefs = cu.topDefs.map(verifyTopDefinition(_)(ctx, global))

    CompilationUnit(cu.filename, cu.pkgName, cu.imports, topDefs, cu.position).setID(cu.id)
  }

  def typedStructDef(structDef: StructDef)(implicit ctx: Context.RootContext, global: GlobalData): StructDef = {
    structDef.symbol.tpe

    val signatureCtx = Context(ctx, structDef.symbol)
    val struct = structDef.symbol.asEntityTypeSymbol

    signatureCtx.reAppend(
      struct.hps ++
      struct.tps: _*
    )

    val result = for {
      _ <- TyperUtil.verifyHPBoundType(struct)(global)
      _ <- TyperUtil.verifyTPBoundType(struct)(signatureCtx, global)
      _ <- verifyHavingErrorType(structDef.fields)
      _ <- verifyHavingErrorType(structDef.hp)
    } yield ()

    result.left.foreach(global.repo.error.append)
    structDef
  }

  def typedModuleDef(moduleDef: ModuleDef)(implicit ctx: Context.RootContext, global: GlobalData): ModuleDef = {
    moduleDef.symbol.tpe

    val signatureCtx = Context(ctx, moduleDef.symbol)
    val module = moduleDef.symbol.asEntityTypeSymbol

    signatureCtx.reAppend(
      module.hps ++
      module.tps: _*
    )

    val result = for {
      _ <- TyperUtil.verifyHPBoundType(module)(global)
      _ <- TyperUtil.verifyTPBoundType(module)(signatureCtx, global)
      _ <- verifyHavingErrorType(moduleDef.parents)
      _ <- verifyHavingErrorType(moduleDef.siblings)
      _ <- verifyHavingErrorType(moduleDef.hp)
    } yield ()

    result.left.foreach(global.repo.error.append)
    moduleDef
  }

  def typedInterfaceDef(interfaceDef: InterfaceDef)(implicit ctx: Context.RootContext, global: GlobalData): InterfaceDef = {
    def verifyModifierValidity: Either[Error, Unit] = {
      val isTrait = interfaceDef.flag.hasFlag(Modifier.Trait)

      val validModifiers =
        if(isTrait) Vector(Modifier.NoModifier, Modifier.Static)
        else Vector(
          Modifier.Sibling | Modifier.Input,
          Modifier.Input,
          Modifier.Internal,
          Modifier.Sibling,
          Modifier.Parent,
          Modifier.Static,
        )

      interfaceDef.methods
        .filterNot(method => validModifiers.contains(method.flag))
        .map(method => Error.InvalidModifier(validModifiers, method.flag))
        .map(Left.apply[Error, Unit])
        .combine(errs => Error.MultipleErrors(errs: _*))
    }

    def verifyMethodValidity: Either[Error, Unit] = {
      val results = interfaceDef.methods.map {
        methodDef =>
          val method = methodDef.symbol.asMethodSymbol
          if(method.tpe.isErrorType) Left(Error.DummyError)
          else Right(())
      }

      results.combine(errs => Error.MultipleErrors(errs: _*))
    }

    interfaceDef.symbol.tpe

    val signatureCtx = Context(ctx, interfaceDef.symbol)
    val interface = interfaceDef.symbol.asInterfaceSymbol
    Type.buildThisType(interface, interfaceDef.hp, interfaceDef.tp)(signatureCtx, global) match {
      case None => interfaceDef
      case Some(tpe) =>
        val bodyCtx = Context(signatureCtx, tpe)

        val result = for {
          _ <- TyperUtil.verifyHPBoundType(interface)(global)
          _ <- TyperUtil.verifyTPBoundType(interface)(bodyCtx, global)
          _ <- verifyModifierValidity
          _ <- verifyMethodValidity
        } yield ()

        interfaceDef.types.foreach(_.symbol.tpe)
        result.left.foreach(global.repo.error.append)

        interfaceDef
    }
  }

  def typedEnumDef(enumDef: EnumDef)(implicit ctx: Context.RootContext, global: GlobalData): EnumDef = {
    def verifyMembers(members: Vector[EnumMemberDef]): Either[Error, Unit] = {
      val errors = members.map(_.symbol.tpe).filter(_.isErrorType)

      if(errors.isEmpty) Right(())
      else Left(Error.DummyError)
    }

    enumDef.symbol.tpe

    val signatureCtx = Context(ctx, enumDef.symbol)
    val enum = enumDef.symbol.asEnumSymbol

    signatureCtx.reAppend(enum.hps ++ enum.tps: _*)

    val bodyCtx = Context(signatureCtx)

    val result = for {
      _ <- TyperUtil.verifyHPBoundType(enum)(global)
      _ <- TyperUtil.verifyTPBoundType(enum)(bodyCtx, global)
      _ <- verifyMembers(enumDef.members)
      _ <- verifyHavingErrorType(enumDef.hp)
    } yield ()

    result.left.foreach(global.repo.error.append)
    enumDef
  }

  def typedImplClassSignature(impl: ImplementClass)(implicit ctx: Context.RootContext, global: GlobalData): ImplementClass = {
    val signatureCtx = Context(ctx, impl.symbol)
    val implSymbol = impl.symbol.asImplementSymbol

    signatureCtx.reAppend(
      implSymbol.hps ++
      implSymbol.tps: _*
    )

    val result = for {
      _ <- TyperUtil.verifyHPBoundType(implSymbol)(global)
      _ <- TyperUtil.verifyTPBoundType(implSymbol)(signatureCtx, global)
      _ <- verifyType(impl.target, signatureCtx, global)
    } yield ()

    result.left.foreach(global.repo.error.append)

    impl
  }

  def typedImplInterfaceSignature(impl: ImplementInterface)(implicit ctx: Context.RootContext, global: GlobalData): ImplementInterface = {
    val signatureCtx = Context(ctx, impl.symbol)
    val implSymbol = impl.symbol.asImplementSymbol

    signatureCtx.reAppend(
      implSymbol.hps ++
      implSymbol.tps: _*
    )

    val result = for {
      _ <- TyperUtil.verifyHPBoundType(implSymbol)(global)
      _ <- TyperUtil.verifyTPBoundType(implSymbol)(signatureCtx, global)
      _ <- verifyType(impl.target, signatureCtx, global)
      _ <- verifyType(impl.interface, signatureCtx, global)
    } yield ()

    impl.types.foreach(_.symbol.tpe)
    result.left.foreach(global.repo.error.append)

    impl
  }

  private def verifyHavingErrorType(vdefs: Vector[ValDef]): Either[Error, Unit] = {
    val hasError = vdefs.view.map(_.symbol.tpe).exists(_.isErrorType)

    if(hasError) Left(Error.DummyError)
    else Right(())
  }

  def verifyTopDefinition(defTree: Definition)(implicit ctx: Context.RootContext, global: GlobalData): Definition =
    defTree match {
      case struct: StructDef => typedStructDef(struct)
      case module: ModuleDef => typedModuleDef(module)
      case interface: InterfaceDef => typedInterfaceDef(interface)
      case enum: EnumDef => typedEnumDef(enum)
      case impl: ImplementClass => typedImplClassSignature(impl)
      case impl: ImplementInterface => typedImplInterfaceSignature(impl)
      case method: MethodDef => method
    }

  private def verifyType(typeTree: TypeTree, ctx: Context.NodeContext, global: GlobalData): Either[Error, Unit] = {
    val typedTypeTree = Typer.typedTypeTree(typeTree)(ctx, global)
    typedTypeTree.tpe match {
      case Type.ErrorType => Left(Error.DummyError)
      case _: Type.RefType => Right(())
    }
  }
}
