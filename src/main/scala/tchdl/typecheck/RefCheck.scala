package tchdl.typecheck

import tchdl.ast._
import tchdl.util._
import tchdl.util.TchdlException.ImplementationErrorException

object RefCheck {
  def exec(cu: CompilationUnit)(implicit global: GlobalData): CompilationUnit = {
    val ctx = getContext(cu.pkgName, cu.filename)

    cu.topDefs.foreach(verify(_)(ctx, global))
    cu
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
          case proc: ProcDef => verifyProcDef(proc)(implCtx, global)
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

  def verifyProcDef(procDef: ProcDef)(implicit ctx: Context.NodeContext, global: GlobalData): Unit = {
    val procCtx = Context(ctx, procDef.symbol.asProcSymbol)

    procDef.blks.foreach{blk =>
      val blkCtx = Context(procCtx, blk.symbol.asProcBlockSymbol)
      val elems = blk.blk.elems :+ blk.blk.last
      elems.foreach {
        case v: ValDef => verifyValDef(v)(blkCtx, global)
        case e: Expression => verifyExpr(e)(blkCtx, global)
        case a: Assign => verifyAssignLoc(a.left)
      }
    }
  }

  def verifyStageDef(stageDef: StageDef)(implicit ctx: Context.NodeContext, global: GlobalData): Unit = {
    val stage = stageDef.symbol.asStageSymbol
    val stageSigCtx = Context(ctx, stage)
    stageSigCtx.reAppend(stageDef.params.map(_.symbol): _*)

    val stageBlkCtx = Context(stageSigCtx)
    stageDef.blk.foreach {
      case Assign(loc, _) => verifyAssignLoc(loc)(stageBlkCtx, global)
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
          case Assign(left, _) => verifyAssignLoc(left)
        }
        verifyExpr(blk.last)(blkCtx, global)
      case _ => // nothing to do
    }

  def verifySelect(select: Select)(implicit ctx: Context.NodeContext, global: GlobalData): Unit = {
    def publicPattern(symbol: Symbol.TermSymbol): Either[Error, Unit] = select.prefix match {
      case _: This if symbol.hasFlag(Modifier.Output) => Left(Error.ReadOutputFromInner(symbol, select.position))
      case _ if symbol.hasFlag(Modifier.Input) => Left(Error.ReadInputFromOuter(symbol, select.position))
      case _ => Right(())
    }

    def privatePattern(symbol: Symbol.TermSymbol): Either[Error, Unit] = select.prefix match {
      case _: This if symbol.hasFlag(Modifier.Output) => Left(Error.ReadOutputFromInner(symbol, select.position))
      case _: This => Right(())
      case _ => Left(Error.ReferPrivate(symbol, select.position))
    }

    verifyExpr(select.prefix)

    val prefixTpe = select.prefix.tpe.asRefType
    prefixTpe.lookupField(select.name, ctx.hpBounds, ctx.tpBounds)(select.position, global) match {
      case LookupResult.LookupSuccess(symbol) =>
        symbol.accessibility match {
          case Accessibility.Public => publicPattern(symbol)
          case Accessibility.Private => privatePattern(symbol)
        }
      case LookupResult.LookupFailure(_) =>
        throw new ImplementationErrorException("looked up field must be found")
    }
  }

  def verifyIfExpr(ifExpr: IfExpr)(implicit ctx: Context.NodeContext, global: GlobalData): Unit = {
    verifyExpr(ifExpr.cond)
    verifyExpr(ifExpr.conseq)
    ifExpr.alt.foreach(verifyExpr)

    val isRetUnit = ifExpr.tpe == Type.unitTpe
    val isRetPointer = ifExpr.tpe.asRefType.isPointer
    val isRetHWTpe = ifExpr.tpe.asRefType.isHardwareType(ctx.tpBounds)(ifExpr.cond.position, global)

    if (!isRetHWTpe && !isRetPointer && !isRetUnit)
      global.repo.error.append(Error.RequirePointerOrHWType(ifExpr.tpe.asRefType, ifExpr.cond.position))
  }

  def verifyApply(apply: Apply)(implicit ctx: Context.NodeContext, global: GlobalData): Unit = {
    def verifyCallWithSymbolPrefix(prefix: Symbol.TermSymbol, method: Symbol.MethodSymbol): Either[Error, Unit] = {
      method.accessibility match {
        case Accessibility.Private => Left(Error.CallPrivate(method, apply.position))
        case Accessibility.Public if prefix.hasFlag(method.flag) => Right(())
        case Accessibility.Public if prefix.hasFlag(Modifier.Child) && method.hasFlag(Modifier.Input) => Right(())
        case Accessibility.Public if method.hasFlag(Modifier.Input) => Left(Error.CallInvalid(method, apply.position))
        case Accessibility.Public if method.hasFlag(Modifier.Sibling) => Left(Error.CallInvalid(method, apply.position))
        case Accessibility.Public if method.hasFlag(Modifier.Parent) => Left(Error.CallInvalid(method, apply.position))
        case Accessibility.Public => Right(())
      }
    }

    apply.prefix match {
      case Select(expr, _) => verifyExpr(expr)
      case _ => // nothing to do
    }

    val result = apply.prefix match {
      case _: Ident => Right(())
      case _: StaticSelect => Right(())
      case select @ Select(_: This, _) =>
        val method = select.symbol.asMethodSymbol
        method.accessibility match {
          case Accessibility.Private => Right(())
          case Accessibility.Public =>
            lazy val isInput = select.symbol.hasFlag(Modifier.Input)
            lazy val isParent = select.symbol.hasFlag(Modifier.Parent)
            lazy val isSibling = select.symbol.hasFlag(Modifier.Sibling)

            if (isInput || isParent || isSibling) Left(Error.CallInterfaceFromInternal(method, select.position))
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
          case _ if prefix.tpe.asRefType.isModuleType => Left(Error.CallInterfaceMustBeDirect(prefix.tpe.asRefType, select.position))
          case Accessibility.Private => Left(Error.CallPrivate(method, select.position))
          case _ => Right(())
        }
    }

    result.left.foreach(global.repo.error.append)
  }

  def verifyAssignLoc(loc: Expression)(implicit ctx: Context.NodeContext, global: GlobalData): Unit = {
    def verifyInnerPattern(symbol: Symbol.TermSymbol): Unit = {
      if(symbol.hasFlag(Modifier.Input))
        global.repo.error.append(Error.WriteInputFromInner(symbol, loc.position))
    }

    def verifyOuterPattern(symbol: Symbol.TermSymbol): Unit = {
      if(symbol.hasFlag(Modifier.Output))
        global.repo.error.append(Error.WriteOutputFromOuter(symbol, loc.position))
    }

    loc match {
      case select @ Select(This(), _) => verifyInnerPattern(select.symbol.asTermSymbol)
      case select @ Select(Select(This(), _), _) => verifyOuterPattern(select.symbol.asTermSymbol)
    }
  }
}