package tchdl.typecheck

import tchdl.ast._
import tchdl.util._
import tchdl.util.TchdlException.ImplementationErrorException

object RefCheck {
  def exec(cu: CompilationUnit)(implicit global: GlobalData): Unit = {
    val ctx = getContext(cu.pkgName, cu.filename.get)

    cu.topDefs.foreach(verify(_)(ctx, global))
  }

  def verify(defTree: Definition)(implicit ctx: Context.RootContext, global: GlobalData): Unit =
    defTree match {
      case impl: ImplementClass =>
        val implSymbol = impl.symbol.asImplementSymbol
        val implSigCtx = Context(ctx, impl.symbol)
        implSigCtx.reAppend(implSymbol.hps ++ implSymbol.tps: _*)

        val implCtx = Context(implSigCtx, impl.target.tpe.asRefType)

        impl.components.foreach {
          case vdef: ValDef => verifyValDef(vdef)(implCtx, global)
          case method: MethodDef => verifyMethodDef(method)(implCtx, global)
          case stage: StageDef => verifyStageDef(stage)(implCtx, global)
          case always: AlwaysDef => verifyAlways(always)(implCtx, global)
        }
      case impl: ImplementInterface =>
        val implSymbol = impl.symbol.asImplementSymbol
        val implSigCtx = Context(ctx, impl.symbol)
        implSigCtx.reAppend(implSymbol.hps ++ implSymbol.tps: _*)

        val implCtx = Context(implSigCtx, impl.target.tpe.asRefType)

        impl.methods.foreach(verifyMethodDef(_)(implCtx, global))
      case _ => // nothing to do
    }

  def verifyValDef(vdef: ValDef)(implicit ctx: Context.NodeContext, global: GlobalData): Unit =
    vdef.expr.foreach(verifyExpr)

  def verifyMethodDef(methodDef: MethodDef)(implicit ctx: Context.NodeContext, global: GlobalData): Unit = {
    val method = methodDef.symbol.asMethodSymbol
    val methodSigCtx = Context(ctx, method)
    methodSigCtx.reAppend(method.hps ++ method.tps: _*)

    methodDef.blk.foreach(verifyExpr(_)(methodSigCtx, global))
  }

  def verifyStageDef(stageDef: StageDef)(implicit ctx: Context.NodeContext, global: GlobalData): Unit = {
    val stage = stageDef.symbol.asStageSymbol
    val stageSigCtx = Context(ctx, stage)
    stageSigCtx.reAppend(stageDef.params.map(_.symbol): _*)

    val stageBlkCtx = Context(stageSigCtx)
    stageDef.blk.foreach {
      case v: ValDef => verifyValDef(v)(stageBlkCtx, global)
      case expr: Expression => verifyExpr(expr)(stageBlkCtx, global)
    }
    stageDef.states.foreach(verifyStateDef(_)(stageBlkCtx, global))
  }

  def verifyStateDef(stateDef: StateDef)(implicit ctx: Context.NodeContext, global: GlobalData): Unit = {
    val state = stateDef.symbol.asStateSymbol
    val stateSigCtx = Context(ctx, state)

    verifyExpr(stateDef.blk)(stateSigCtx, global)
  }

  def verifyAlways(alwaysDef: AlwaysDef)(implicit ctx: Context.NodeContext, global: GlobalData): Unit = {
    val alwaysCtx = Context(ctx, alwaysDef.symbol)
    verifyExpr(alwaysDef.blk)(alwaysCtx, global)
  }


  def verifyExpr(expr: Expression)(implicit ctx: Context.NodeContext, global: GlobalData): Unit =
    expr match {
      case select: Select => verifySelect(select)
      case ifExpr: IfExpr => verifyIfExpr(ifExpr)
      case apply: Apply => verifyApply(apply)
      case blk: Block =>
        val blkCtx = Context.blk(ctx)
        blk.elems.foreach {
          case expr: Expression => verifyExpr(expr)(blkCtx, global)
          case ValDef(_, _, _, expr) => expr.foreach(verifyExpr(_)(blkCtx, global))
        }
        verifyExpr(blk.last)(blkCtx, global)
      case _ => // nothing to do
    }

  def verifySelect(select: Select)(implicit ctx: Context.NodeContext, global: GlobalData): Unit = {
    verifyExpr(select.prefix)

    val prefixTpe = select.prefix.tpe.asRefType
    prefixTpe.lookupField(select.name) match {
      case LookupResult.LookupSuccess(symbol) => symbol.accessibility match {
        case Accessibility.Public => Right(())
        case Accessibility.Private => select.prefix match {
          case _: This => Right(())
          case _ => Left(Error.ReferPrivate(symbol))
        }
      }
      case LookupResult.LookupFailure(_) =>
        throw new ImplementationErrorException("looked up field must be found")
    }
  }

  def verifyIfExpr(ifExpr: IfExpr)(implicit ctx: Context.NodeContext, global: GlobalData): Unit = {
    verifyExpr(ifExpr.cond)
    verifyExpr(ifExpr.conseq)
    ifExpr.alt.foreach(verifyExpr)

    val isCondBit1 = ifExpr.cond.tpe =:= Type.bitTpe(IntLiteral(1))
    val isRetUnit = ifExpr.tpe =:= Type.unitTpe
    val isRetHWTpe = ifExpr.tpe.asRefType.isHardwareType

    if (isCondBit1 && !isRetHWTpe && !isRetUnit)
      global.repo.error.append(Error.RequireHardwareType(ifExpr.tpe.asRefType))
  }

  def verifyApply(apply: Apply)(implicit ctx: Context.NodeContext, global: GlobalData): Unit = {
    def verifyCallWithSymbolPrefix(prefix: Symbol.TermSymbol, method: Symbol.MethodSymbol): Either[Error, Unit] = {
      method.accessibility match {
        case Accessibility.Private => Left(Error.CallPrivate(method))
        case Accessibility.Public if prefix.hasFlag(method.flag) => Right(())
        case Accessibility.Public if prefix.flag == Modifier.NoModifier && method.hasFlag(Modifier.Input) => Right(())
        case Accessibility.Public if method.hasFlag(Modifier.Input) => Left(Error.CallInvalid(method))
        case Accessibility.Public if method.hasFlag(Modifier.Sibling) => Left(Error.CallInvalid(method))
        case Accessibility.Public if method.hasFlag(Modifier.Parent) => Left(Error.CallInvalid(method))
        case Accessibility.Public => Right(())
      }
    }

    apply.prefix match {
      case Select(expr, _) => verifyExpr(expr)
      case _ => // nothing to do
    }

    val result = apply.prefix match {
      case select @ Select(_: This, _) =>
        val method = select.symbol.asMethodSymbol
        method.accessibility match {
          case Accessibility.Private => Right(())
          case Accessibility.Public =>
            lazy val isInput = select.symbol.hasFlag(Modifier.Input)
            lazy val isParent = select.symbol.hasFlag(Modifier.Parent)
            lazy val isSibling = select.symbol.hasFlag(Modifier.Sibling)

            if (isInput || isParent || isSibling) Left(Error.CallInterfaceFromInternal(method))
            else Right(())
        }
      case select @ Select(prefix: Ident, _) =>
        val method = select.symbol.asMethodSymbol
        verifyCallWithSymbolPrefix(prefix.symbol.asTermSymbol, method)
      case select @ Select(prefix: Select, _) =>
        val method = select.symbol.asMethodSymbol
        verifyCallWithSymbolPrefix(prefix.symbol.asTermSymbol, method)
      case select @ Select(prefix, _) =>
        val method = select.symbol.asMethodSymbol
        method.accessibility match {
          case _ if prefix.tpe.asRefType.isModuleType => Left(Error.CallInterfaceMustBeDirect(prefix.tpe.asRefType))
          case Accessibility.Private => Left(Error.CallPrivate(method))
          case _ => Right(())
        }
    }

    result.left.foreach(global.repo.error.append)
  }
}