package tchdl.typecheck

import tchdl.ast._
import tchdl.util._
import tchdl.util.TchdlException.ImplementationErrorException

object RefCheck {
  def exec(cu: CompilationUnit)(implicit global: GlobalData): Unit = {
    val ctx = getContext(cu.pkgName, cu.filename.get)
  }

  def verifyModuleDef(moduleDef: ModuleDef)(implicit ctx: Context.RootContext, global: GlobalData): Unit = {
    val sigCtx = Context(ctx, moduleDef.symbol)
    val module = moduleDef.symbol.asModuleSymbol
    sigCtx.reAppend(module.hps ++ module.tps: _*)

    def verifyModuleTypes(tpes: Vector[Type.RefType]): Either[Error, Unit] = {
      val errors = tpes
        .filterNot(_.isModuleType(sigCtx, global))
        .map(tpe => Left(Error.RequireModuleType(tpe)))

      if(errors.isEmpty) Right()
      else Left(Error.MultipleErrors(errors.map{case Left(err) => err}: _*))
    }

    val parentResult = verifyModuleTypes(moduleDef.parents.map(_.symbol.tpe.asRefType))
    val siblingResult = verifyModuleTypes(moduleDef.siblings.map(_.symbol.tpe.asRefType))
    val result = (parentResult, siblingResult) match {
      case (Left(err0), Left(err1)) => Left(Error.MultipleErrors(err0, err1))
      case (left @ Left(_), _) => left
      case (_, left @ Left(_)) => left
      case _ => Right(())
    }

    result.left.foreach(global.repo.error.append)
  }

  def verifyModuleInterfaceMethod(methodDef: MethodDef)(implicit ctx: Context.NodeContext, global: GlobalData): Unit = {
    def verifyNoPolyParams(method: Symbol.MethodSymbol): Either[Error, Unit] = {
      lazy val hasHPTree = methodDef.hp.nonEmpty
      lazy val hasTPTree = methodDef.tp.nonEmpty
      lazy val hasHP = method.hps.nonEmpty
      lazy val hasTP = method.tps.nonEmpty
      val hasPolyParams = hasHPTree || hasTPTree || hasHP || hasTP

      if(hasPolyParams) Left(Error.RejectPolyParams)
      else Right(())
    }

    def verifySignatureTypes(methodType: Type.MethodType)(implicit ctx: Context.NodeContext): Either[Error, Unit] = {
      val paramResult = methodType.params.map { tpe =>
        if(tpe.isHardwareType) Right(())
        else Left(Error.RequireHardwareType(tpe))
      }.combine(errs => Error.MultipleErrors(errs: _*))

      val retResult = {
        val retTpe = methodType.returnType

        if(retTpe.isHardwareType || retTpe =:= Type.unitTpe) Right(())
        else Left(Error.RequireHardwareType(retTpe))
      }

      (paramResult, retResult) match {
        case (Left(err0), Left(err1)) => Left(Error.MultipleErrors(err0, err1))
        case (left @ Left(_), _) => left
        case (_, left @ Left(_)) => left
        case _ => Right(())
      }
    }

    val method = methodDef.symbol.asMethodSymbol
    val sigCtx = Context(ctx, method)
    sigCtx.reAppend(method.hps ++ method.tps: _*)

    val result = (verifyNoPolyParams(method), verifySignatureTypes(method.tpe.asMethodType)(sigCtx)) match {
      case (Left(err0), Left(err1)) => Left(Error.MultipleErrors(err0, err1))
      case (left @ Left(_), _) => left
      case (_, left @ Left(_)) => left
      case _ => Right(())
    }

    result.left.foreach(global.repo.error.append)
  }

  def verifyIfExpr(ifExpr: IfExpr)(implicit ctx: Context.NodeContext, global: GlobalData): Unit = {
    val isCondBit1 = ifExpr.cond.tpe =:= Type.bitTpe(IntLiteral(1))
    val isRetHWTpe = ifExpr.tpe.asRefType.isHardwareType

    if(isCondBit1 && !isRetHWTpe) {
      global.repo.error.append(Error.RequireHardwareType(ifExpr.tpe.asRefType))
    }
  }

  def verifyApply(apply: Apply)(implicit ctx: Context.NodeContext, global: GlobalData): Unit = {
    verifyExpr(apply.prefix)
    val result = apply.prefix match {
      case select @ Select(_: This, _) => select.symbol.accessibility match {
        case Accessibility.Private => Right(())
        case Accessibility.Public =>
          lazy val isInput = select.symbol.hasFlag(Modifier.Input)
          lazy val isParent = select.symbol.hasFlag(Modifier.Parent)
          lazy val isSibling = select.symbol.hasFlag(Modifier.Sibling)

          if(isInput || isParent || isSibling) Left(???)
          else Right(())
      }
      case select: Select => select.symbol.accessibility match {
        case Accessibility.Public => Right(())
        case Accessibility.Private => Left(???)
      }
    }

    result.left.foreach(global.repo.error.append)
  }

  def verifyExpr(expr: Expression)(implicit ctx: Context.NodeContext, global: GlobalData): Unit = {

  }
}