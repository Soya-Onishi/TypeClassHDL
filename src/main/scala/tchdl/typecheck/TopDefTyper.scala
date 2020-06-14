package tchdl.typecheck

import tchdl.util.TchdlException._
import tchdl.util._
import tchdl.ast._

object TopDefTyper {
  def exec(cu: CompilationUnit)(implicit global: GlobalData): CompilationUnit = {
    val ctx = global.rootPackage.search(cu.pkgName)
      .getOrElse(throw new ImplementationErrorException(s"${cu.pkgName} should be there"))
      .lookupCtx(cu.filename.get)
      .getOrElse(throw new ImplementationErrorException(s"${cu.filename.get}'s context should be there'"))

    val topDefs = cu.topDefs.map(verifyTopDefinition(_)(ctx, global))

    CompilationUnit(cu.filename, cu.pkgName, cu.imports, topDefs).setID(cu.id)
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
      _ <- verifyTPBoundType(struct)(signatureCtx)
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
      _ <- verifyTPBoundType(module)(signatureCtx)
      _ <- verifyHavingErrorType(moduleDef.parents)
      _ <- verifyHavingErrorType(moduleDef.siblings)
      _ <- verifyHavingErrorType(moduleDef.hp)
    } yield ()

    result.left.foreach(global.repo.error.append)
    moduleDef
  }

  def typedInterfaceDef(interfaceDef: InterfaceDef)(implicit ctx: Context.RootContext, global: GlobalData): InterfaceDef = {
    def verifyMethodValidity: Either[Error, Unit] = {
      val methodTypes = interfaceDef.methods.map(_.symbol.tpe)

      if(methodTypes.exists(_.isErrorType)) Left(Error.DummyError)
      else Right(())
    }

    interfaceDef.symbol.tpe

    val signatureCtx = Context(ctx, interfaceDef.symbol)
    val interface = interfaceDef.symbol.asInterfaceSymbol

    val result = for {
      _ <- verifyTPBoundType(interface)(signatureCtx)
      _ <- verifyMethodValidity
    } yield ()

    result.left.foreach(global.repo.error.append)
    interfaceDef
  }

  def typedImplClassSignature(impl: ImplementClass)(implicit ctx: Context.RootContext, global: GlobalData): ImplementClass = {
    val signatureCtx = Context(ctx, impl.symbol)
    val implSymbol = impl.symbol.asImplementSymbol

    val result = for {
      _ <- verifyTPBoundType(implSymbol)(signatureCtx)
      _ <- verifyType(impl.target, signatureCtx, global)
    } yield ()

    result.left.foreach(global.repo.error.append)

    impl
  }

  def typedImplInterfaceSignature(impl: ImplementInterface)(implicit ctx: Context.RootContext, global: GlobalData): ImplementInterface = {
    val signatureCtx = Context(ctx, impl.symbol)
    val implSymbol = impl.symbol.asImplementSymbol

    val result = for {
      _ <- verifyTPBoundType(implSymbol)(signatureCtx)
      _ <- verifyType(impl.target, signatureCtx, global)
      _ <- verifyType(impl.interface, signatureCtx, global)
    } yield ()

    result.left.foreach(global.repo.error.append)

    impl
  }

  def verifyTopDefinition(defTree: Definition)(implicit ctx: Context.RootContext, global: GlobalData): Definition =
    defTree match {
      case struct: StructDef => typedStructDef(struct)
      case module: ModuleDef => typedModuleDef(module)
      case interface: InterfaceDef => typedInterfaceDef(interface)
      case impl: ImplementClass => typedImplClassSignature(impl)
      case impl: ImplementInterface => typedImplInterfaceSignature(impl)
    }


  private def verifyTPBoundType(symbol: Symbol with HasParams)(implicit ctx: Context.NodeContext): Either[Error, Unit] = {
    def verifyEachBounds(hpBounds: Vector[HPBound], tpBounds: Vector[TPBound])(implicit ctx: Context.NodeContext): Either[Error, Unit] = {
      val (hpErrs, _) = hpBounds.map(HPBound.verifyMeetBound(_, ctx.hpBounds)).partitionMap(identity)
      val (tpErrs, _) = tpBounds.map(TPBound.verifyMeetBound(_, ctx.hpBounds, ctx.tpBounds)).partitionMap(identity)
      val errs = hpErrs ++ tpErrs

      if(errs.isEmpty) Right(())
      else Left(Error.MultipleErrors(errs: _*))
    }

    val tpBounds = symbol.tpBound
    val results = tpBounds.flatMap{ tpBound => tpBound.bounds.map{
      bound =>
        val symbol = bound.origin.asInterfaceSymbol
        val hpTable = (symbol.hps zip bound.hardwareParam).toMap
        val tpTable = (symbol.tps zip bound.typeParam).toMap
        val replacedHPBound = HPBound.swapBounds(symbol.hpBound, hpTable)
        val replacedTPBound = TPBound.swapBounds(symbol.tpBound, hpTable, tpTable)

        verifyEachBounds(replacedHPBound, replacedTPBound)
    }}

    val (errs, _) = results.partitionMap(identity)

    if(errs.isEmpty) Right(())
    else Left(Error.MultipleErrors(errs: _*))
  }

  private def verifyHavingErrorType(vdefs: Vector[ValDef]): Either[Error, Unit] = {
    val hasError = vdefs.view.map(_.symbol.tpe).exists(_.isErrorType)

    if(hasError) Left(Error.DummyError)
    else Right(())
  }

  private def verifyType(typeTree: TypeTree, ctx: Context.NodeContext, global: GlobalData): Either[Error, Unit] = {
    val typedTypeTree = Typer.typedTypeTree(typeTree)(ctx, global)
    typedTypeTree.tpe match {
      case Type.ErrorType => Left(Error.DummyError)
      case _: Type.RefType => Right(())
    }
  }
}
