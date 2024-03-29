package tchdl.typecheck

import tchdl.ast._
import tchdl.util.TchdlException.ImplementationErrorException
import tchdl.util._

import scala.annotation.tailrec

object Typer {
  def exec(cu: CompilationUnit)(implicit global: GlobalData): CompilationUnit = {
    implicit val ctx: Context.RootContext = getContext(cu.pkgName, cu.filename)

    val topDefs = cu.topDefs.map(diveIntoExpr)

    CompilationUnit(cu.filename, cu.pkgName, cu.imports, topDefs, cu.position)
  }

  def diveIntoExpr(defTree: Definition)(implicit ctx: Context.RootContext, global: GlobalData): Definition = {
    defTree match {
      case impl: ImplementClass =>
        val implSymbol = impl.symbol.asImplementSymbol
        val implSigCtx = Context(ctx, implSymbol)
        implSigCtx.reAppend(implSymbol.hps ++ implSymbol.tps: _*)

        val implBodyCtx = Context(implSigCtx, impl.target.tpe.asRefType)

        val typedComponents = impl.components.map {
          case methodDef: MethodDef => typedMethodDef(methodDef)(implBodyCtx, global)
          case stageDef: StageDef => typedStageDef(stageDef)(implBodyCtx, global)
          case alwaysDef: AlwaysDef => typedAlwaysDef(alwaysDef)(implBodyCtx, global)
          case procDef: ProcDef => typedProcDef(procDef)(implBodyCtx, global)
          case valDef: ValDef if valDef.flag.hasNoFlag(Modifier.Child) => typedValDef(valDef)(implBodyCtx, global)
          case valDef: ValDef => typedModDef(valDef)(implBodyCtx, global)
        }

        val typedImpl = impl.copy(components = typedComponents).setSymbol(impl.symbol).setID(impl.id)
        global.cache.set(typedImpl)
        typedImpl
      case impl: ImplementInterface =>
        val implSymbol = impl.symbol.asImplementSymbol
        val implSigCtx = Context(ctx, implSymbol)
        implSigCtx.reAppend(implSymbol.hps ++ implSymbol.tps: _*)

        val implBodyCtx = Context(implSigCtx, impl.target.tpe.asRefType)
        val typedMethods = impl.methods.map(typedMethodDef(_)(implBodyCtx, global))

        val typedImpl = impl.copy(methods = typedMethods).setSymbol(impl.symbol).setID(impl.id)
        global.cache.set(typedImpl)
        typedImpl
      case method: MethodDef => typedMethodDef(method)
      case others => others
    }
  }

  def typedMethodDef(methodDef: MethodDef)(implicit ctx: Context, global: GlobalData): MethodDef = {
    val method = methodDef.symbol.asMethodSymbol
    val methodTpe = method.tpe.asMethodType
    val isStatic = methodDef.symbol.hasFlag(Modifier.Static)
    val methodSigCtx = Context(ctx, method, isStatic = isStatic)
    methodSigCtx.reAppend(method.hps ++ method.tps ++ methodDef.params.map(_.symbol.asVariableSymbol): _*)

    val body = methodDef.blk
      .getOrElse(throw new ImplementationErrorException("methods in impl should have their body"))

    val typedBody = typedBlock(body)(methodSigCtx, global)

    if (!typedBody.tpe.isErrorType && typedBody.tpe.asRefType != methodTpe.returnType)
      global.repo.error.append(Error.TypeMismatch(methodTpe.returnType, typedBody.tpe.asRefType, typedBody.last.position))

    methodDef.copy(blk = Some(typedBody)).setSymbol(methodDef.symbol).setID(methodDef.id)
  }

  def typedAlwaysDef(always: AlwaysDef)(implicit ctx: Context.NodeContext, global: GlobalData): AlwaysDef = {
    val alwaysCtx = Context(ctx, always.symbol)
    val typedBlk = typedBlock(always.blk)(alwaysCtx, global)

    val typedAlways = always.copy(
      always.name,
      typedBlk
    )
      .setSymbol(always.symbol)
      .setID(always.id)

    global.cache.set(typedAlways)
    typedAlways
  }

  def typedProcDef(pdef: ProcDef)(implicit ctx: Context.NodeContext, global: GlobalData): ProcDef = {
    val procCtx = Context(ctx, pdef.symbol)
    val typedDefault = typedExpr(pdef.default)(procCtx, global)

    // named and typed each blocks in proc
    val typedBlocks = pdef.blks.map(typedProcBlock(_)(procCtx, global))

    val retTpe = pdef.symbol.tpe.asMethodType.returnType
    val expectTpe = Type.RefType(retTpe.origin, retTpe.hardwareParam, retTpe.typeParam, isPointer = false)
    if(typedDefault.tpe != expectTpe && !typedDefault.tpe.isErrorType)
      global.repo.error.append(Error.TypeMismatch(expectTpe, typedDefault.tpe.asRefType, typedDefault.position))

    val typedPDef = pdef.copy(
      default = typedDefault,
      blks = typedBlocks,
    )

    global.cache.set(typedPDef)
    typedPDef
  }

  def typedProcBlock(pblk: ProcBlock)(implicit ctx: Context.NodeContext, global: GlobalData): ProcBlock = {
    val sigCtx = Context(ctx, pblk.symbol)

    // named and typed parameters
    pblk.symbol.tpe
    val paramSymbols = pblk.params.map(_.symbol)
    sigCtx.reAppend(paramSymbols: _*)

    val typedBlk = typedBlock(pblk.blk)(sigCtx, global)
    val typedPBlk = pblk.copy(blk = typedBlk)

    global.cache.set(typedPBlk)
    typedPBlk
  }

  def typedValDef(vdef: ValDef)(implicit ctx: Context.NodeContext, global: GlobalData): ValDef = {
    val vdefTpe = vdef.symbol.tpe

    val typedTpeTree = vdef.tpeTree.flatMap(global.cache.get) match {
      case Some(tree: TypeTree) => Some(tree)
      case None => vdef.tpeTree.map(typedTypeTree)
    }

    val typedExpression = vdef.expr.flatMap(global.cache.get) match {
      case Some(expr: Expression) => Some(expr)
      case None => vdef.expr.map(typedExpr)
    }

    typedTpeTree.foreach(global.cache.set)
    typedExpression.foreach(global.cache.set)

    if (!vdefTpe.isErrorType) {
      def typecheck(tree: Option[AST with HasType]): Unit = {
        tree.filterNot(_.tpe.isErrorType)
          .filter(_.tpe != vdefTpe)
          .foreach(t => global.repo.error.append(Error.TypeMismatch(vdefTpe, t.tpe, t.position)))
      }

      typecheck(typedTpeTree)
      typecheck(typedExpression)
    }

    vdef.copy(tpeTree = typedTpeTree, expr = typedExpression)
      .setSymbol(vdef.symbol)
      .setID(vdef.id)
  }

  def typedModDef(valDef: ValDef)(implicit ctx: Context.NodeContext, global: GlobalData): ValDef = {
    val ValDef(_, name, tpe, Some(construct)) = valDef
    val typedTpeTree = tpe.map(typedTypeTree)

    val typedConstruct = construct match {
      case construct: ConstructClass => typedConstructClass(construct)
      case construct: ConstructModule => typedConstructModule(construct)
    }

    typedTpeTree.map(_.tpe)
      .filterNot(tpe => tpe.isErrorType)
      .filterNot(_ => typedConstruct.tpe.isErrorType)
      .filter(_ != typedConstruct.tpe.asRefType)
      .map(tpe => Error.TypeMismatch(tpe, typedConstruct.tpe.asRefType, typedConstruct.position))
      .foreach(global.repo.error.append)

    val typedValDef = ValDef(valDef.flag, name, typedTpeTree, Some(typedConstruct), valDef.position)
      .setSymbol(valDef.symbol)
      .setID(valDef.id)

    global.cache.set(typedValDef)

    typedValDef
  }

  def typedExprValDef(vdef: ValDef)(implicit ctx: Context.NodeContext, global: GlobalData): ValDef = {
    Namer.namedLocalDef(vdef)

    val result = vdef.symbol.tpe match {
      case Type.ErrorType => Left(Error.DummyError)
      case vdefTpe: Type.RefType =>
        val vdefExpr = vdef.expr.getOrElse(throw new ImplementationErrorException("variable definition in the block should have expression in right"))
        val typedExpr = global.cache.get(vdefExpr) match {
          case Some(expr: Expression) => expr
          case None => this.typedExpr(vdefExpr)
        }

        typedExpr.tpe match {
          case Type.ErrorType => Left(Error.DummyError)
          case exprTpe: Type.RefType if exprTpe != vdefTpe => Left(Error.TypeMismatch(vdefTpe, exprTpe, typedExpr.position))
          case _: Type.RefType => Right(typedExpr)
        }
    }

    result match {
      case Right(expr) =>
        val typeTree = vdef.tpeTree.map(_.setTpe(vdef.symbol.tpe))
        vdef.copy(tpeTree = typeTree, expr = Some(expr))
          .setSymbol(vdef.symbol)
          .setID(vdef.id)
      case Left(err) =>
        global.repo.error.append(err)
        vdef
    }
  }

  def typedStageDef(stageDef: StageDef)(implicit ctx: Context.NodeContext, global: GlobalData): StageDef = {
    val stage = stageDef.symbol.asStageSymbol
    val stageSigCtx = Context(ctx, stage)
    stageSigCtx.reAppend(stageDef.params.map(_.symbol.asVariableSymbol): _*)

    val stageBodyCtx = Context(stageSigCtx)
    stageDef.states.foreach(Namer.namedStateDef(_)(stageBodyCtx, global))

    val typedBodyElems = stageDef.blk.map {
      case assign: Assign => typedAssign(assign)(stageBodyCtx, global)
      case vdef: ValDef => typedExprValDef(vdef)(stageBodyCtx, global)
      case expr: Expression => typedExpr(expr)(stageBodyCtx, global)
    }
    val typedStates = stageDef.states.map(typedStateDef(_)(stageBodyCtx, global))

    stageDef.copy(states = typedStates, blk = typedBodyElems).setSymbol(stageDef.symbol.asStageSymbol).setID(stageDef.id)
  }

  def typedStateDef(stateDef: StateDef)(implicit ctx: Context.NodeContext, global: GlobalData): StateDef = {
    stateDef.symbol.tpe

    val stateSigCtx = Context(ctx, stateDef.symbol)
    stateSigCtx.reAppend(stateDef.params.map(_.symbol): _*)

    val typedBlk = typedBlock(stateDef.blk)(stateSigCtx, global)

    stateDef.copy(blk = typedBlk)
      .setSymbol(stateDef.symbol)
      .setID(stateDef.id)
  }

  def typedExpr(expr: Expression)(implicit ctx: Context.NodeContext, global: GlobalData): Expression =
    expr match {
      case ident: Ident => typedExprIdent(ident)
      case select: Select => typedExprSelect(select)
      case matchExpr: Match => typedMatch(matchExpr)
      case binop: StdBinOp => typedStdBinOp(binop)
      case unaryOp: StdUnaryOp => typedStdUnaryOp(unaryOp)
      case deref: DeReference => typedDeReference(deref)
      case ifExpr: IfExpr => typedIfExpr(ifExpr)
      case self: This => typedThis(self)
      case blk: Block => typedBlock(blk)
      case construct: ConstructClass => typedConstructClass(construct)
      case construct: ConstructModule => typedConstructModule(construct)
      case construct: ConstructEnum => typedConstructEnum(construct)
      case cast: CastExpr => typedCastExpr(cast)
      case int: IntLiteral => typedIntLiteral(int)
      case bool: BoolLiteral => typedBoolLiteral(bool)
      case unit: UnitLiteral => typedUnitLiteral(unit)
      case bit: BitLiteral => typedBitLiteral(bit)
      case apply: Apply => typedExprApply(apply)
      case generate: Generate => typedGenerate(generate)
      case commence: Commence => typedCommence(commence)
      case goto: Goto => typedGoto(goto)
      case finish: Finish => typedFinish(finish)
      case relay: Relay => typedRelay(relay)
      case ret: Return => typedReturn(ret)
      case select: StaticSelect => throw new ImplementationErrorException("StaticSelect must not appear here")
    }

  def typedExprIdent(ident: Ident)(implicit ctx: Context.NodeContext, global: GlobalData): Ident = {
    ctx.lookupLocal[Symbol.VariableSymbol](ident.name) match {
      case LookupResult.LookupFailure(err) =>
        global.repo.error.append(err)
        ident.setTpe(Type.ErrorType).setSymbol(Symbol.ErrorSymbol)
      case LookupResult.LookupSuccess(symbol) =>
        ident.setSymbol(symbol).setTpe(symbol.tpe)
    }
  }

  def typedExprApply(apply: Apply)(implicit ctx: Context.NodeContext, global: GlobalData): Apply = {
    val typedArgs = apply.args.map(typedExpr)
    val typedHPs = apply.hps.map(typedHPExpr)
    val typedTPs = apply.tps.map(typedTypeTree)

    val hasError =
      typedArgs.exists(_.tpe.isErrorType) ||
      typedHPs.exists(_.tpe.isErrorType) ||
      typedTPs.exists(_.tpe.isErrorType)

    lazy val errorApply =
      Apply(apply.prefix, typedHPs, typedTPs, typedArgs, apply.position)
        .setTpe(Type.ErrorType)
        .setID(apply.id)

    def lookupMethodForIdent(ident: Ident): Either[Error, Apply] = {
      def verifyMethodValidity(method: Symbol.MethodSymbol): Either[Error, Unit] = {
        method.tpe match {
          case Type.ErrorType => Left(Error.DummyError)
          case tpe: Type.MethodType =>
            if ((tpe.params :+ tpe.returnType).exists(_.isErrorType)) Left(Error.DummyError)
            else if (method.hps.exists(_.tpe.isErrorType)) Left(Error.DummyError)
            else Right(())
        }
      }

      def verifyLength(methodSymbol: Symbol.MethodSymbol, methodType: Type.MethodType, signaturePos: Position): Either[Error, Unit] = {
        def verify(builder: (Int, Int, Position) => Error)(expect: Int, actual: Int, errs: Vector[Error]): Vector[Error] =
          if (expect == actual) errs
          else errs :+ builder(expect, actual, signaturePos)

        val expectArgLength = methodType.params.length
        val actualArgLength = typedArgs.length
        val expectHPLength = methodSymbol.hps.length
        val actualHPLength = typedHPs.length
        val expectTPLength = methodSymbol.tps.length
        val actualTPLength = typedTPs.length
        val lengthPairs = Seq(
          (expectArgLength, actualArgLength, Error.ParameterLengthMismatch.apply _),
          (expectHPLength, actualHPLength, Error.HardParameterLengthMismatch.apply _),
          (expectTPLength, actualTPLength, Error.TypeParameterLengthMismatch.apply _)
        )

        val errs = lengthPairs.foldLeft(Vector.empty[Error]) {
          case (errs, (expect, actual, builder)) => verify(builder)(expect, actual, errs)
        }

        if (errs.isEmpty) Right(())
        else Left(Error.MultipleErrors(errs: _*))
      }

      def verifyHPType(methodSymbol: Symbol.MethodSymbol): Either[Error, Unit] = {
        val results = (methodSymbol.hps.map(_.tpe) zip typedHPs)
          .map {
            case (p: Type.RefType, a) =>
              if (p == a.tpe) Right(())
              else Left(Error.TypeMismatch(p, a.tpe, a.position))
          }

        val (errs, _) = results.partitionMap(identity)
        if (errs.isEmpty) Right(())
        else Left(Error.MultipleErrors(errs: _*))
      }

      def verifyEachBounds(hpBounds: Vector[HPBound], tpBounds: Vector[TPBound]): Either[Error, Unit] = {
        val (hpErrs, _) = hpBounds.map(HPBound.verifyMeetBound(_, ctx.hpBounds)).partitionMap(identity)
        val (tpErrs, _) = tpBounds.map(TPBound.verifyMeetBound(_, ctx.hpBounds, ctx.tpBounds, apply.position)).partitionMap(identity)
        val errs = hpErrs ++ tpErrs

        if (errs.isEmpty) Right(())
        else Left(Error.MultipleErrors(errs: _*))
      }

      val signatureStart = apply.prefix.position.end
      val signatureEnd = apply.prefix.position.end
      val signaturePos = Position(apply.position.filename, signatureStart, signatureEnd)

      ctx.root.lookup[Symbol.MethodSymbol](ident.name) match {
        case LookupResult.LookupFailure(err) => Left(err)
        case LookupResult.LookupSuccess(methodSymbol) => for {
          _ <- verifyMethodValidity(methodSymbol)
          methodType = methodSymbol.tpe.asMethodType
          _ <- verifyLength(methodSymbol, methodType, signaturePos)
          _ <- verifyHPType(methodSymbol)
          hpTable = (methodSymbol.hps zip typedHPs).toMap
          tpTable = (methodSymbol.tps zip typedTPs.map(_.tpe.asRefType)).toMap
          swappedHPBound = HPBound.swapBounds(methodSymbol.hpBound, hpTable)
          swappedTPBound = TPBound.swapBounds(methodSymbol.tpBound, hpTable, tpTable)
          _ <- verifyEachBounds(swappedHPBound, swappedTPBound)
          replacedTpe = methodType.replaceWithMap(hpTable, tpTable)
          _ <- Type.RefType.verifyMethodType(replacedTpe, typedArgs.map(_.tpe.asRefType), apply.position)
          typedApply = Apply(
            ident.setTpe(replacedTpe).setSymbol(methodSymbol),
            typedHPs,
            typedTPs,
            typedArgs,
            apply.position
          ).setTpe(replacedTpe.returnType).setID(apply.id)
        } yield typedApply
      }
    }

    def lookup(prefixTpe: Type.RefType, name: String, requireStatic: Boolean): Either[Error, (Symbol.MethodSymbol, Type.MethodType)] = {
      val method = prefixTpe.lookupMethod(
        name,
        typedHPs,
        typedTPs.map(_.tpe.asRefType),
        typedArgs.map(_.tpe.asRefType),
        ctx.hpBounds,
        ctx.tpBounds,
        requireStatic
      )(ctx, apply.position, global)

      method.toEither
    }

    def lookupMethodForSelect(select: Select): Either[Error, Apply] = {
      def verifyPrefixType(tpe: Type): Either[Error, Type.RefType] = tpe match {
        case Type.ErrorType => Left(Error.DummyError)
        case tpe: Type.RefType => Right(tpe)
      }

      val typedPrefix = typedExpr(select.prefix)

      for {
        prefixTpe <- verifyPrefixType(typedPrefix.tpe)
        result <- lookup(prefixTpe, select.name, requireStatic = false)
        typedApply = {
          val (symbol, tpe) = result
          val typedSelect =
            Select(typedPrefix, select.name, select.position)
              .setSymbol(symbol)
              .setTpe(tpe)
              .setID(select.id)

          Apply(typedSelect, typedHPs, typedTPs, typedArgs, apply.position)
            .setTpe(tpe.returnType)
            .setID(apply.id)
        }
      } yield typedApply
    }

    def lookupMethodForStaticSelect(select: StaticSelect): Either[Error, Apply] = {
      def verifyPrefixType(tpe: Type): Either[Error, Type.RefType] =
        tpe match {
          case Type.ErrorType => Left(Error.DummyError)
          case tpe: Type.RefType => Right(tpe)
        }

      val prefixTree = typedTypeTree(select.prefix)

      for {
        prefixTpe <- verifyPrefixType(prefixTree.tpe)
        result <- lookup(prefixTpe, select.name, requireStatic = true)
      } yield {
        val (symbol, tpe) = result
        val typedSelect =
          StaticSelect(prefixTree, select.name, select.position)
            .setTpe(tpe)
            .setSymbol(symbol)
            .setID(select.id)

        Apply(typedSelect, typedHPs, typedTPs, typedArgs, apply.position)
          .setTpe(tpe.returnType)
          .setID(apply.id)
      }
    }

    if (hasError) errorApply
    else {
      val result = apply.prefix match {
        case ident: Ident => lookupMethodForIdent(ident)
        case select: Select => lookupMethodForSelect(select)
        case select: StaticSelect => lookupMethodForStaticSelect(select)
      }

      result match {
        case Right(apply) => apply
        case Left(err) =>
          global.repo.error.append(err)
          errorApply
      }
    }
  }

  def typedExprSelect(select: Select)(implicit ctx: Context.NodeContext, global: GlobalData): Select = {
    val typedPrefix = typedExpr(select.prefix)
    typedPrefix.tpe match {
      case refTpe: Type.RefType =>
        // This method only for reference to field of struct or module.
        // That's why this method does not look up method.
        refTpe.lookupField(select.name, ctx.hpBounds, ctx.tpBounds)(select.position, global) match {
          case LookupResult.LookupFailure(err) =>
            global.repo.error.append(err)
            select.copy(typedPrefix, select.name)
              .setTpe(Type.ErrorType)
              .setSymbol(Symbol.ErrorSymbol)
              .setID(select.id)
          case LookupResult.LookupSuccess(symbol) =>
            val tpTable =
              refTpe.origin match {
                case _: Symbol.TypeParamSymbol => Map.empty[Symbol.TypeParamSymbol, Type.RefType]
                case tpe: Symbol.EntityTypeSymbol =>
                  (tpe.tps zip refTpe.typeParam)
                    .map { case (sym, tpe) => sym -> tpe }
                    .toMap
              }

            val hpTable =
              refTpe.origin match {
                case _: Symbol.TypeParamSymbol => Map.empty[Symbol.HardwareParamSymbol, HPExpr]
                case tpe: Symbol.EntityTypeSymbol =>
                  (tpe.hps zip refTpe.hardwareParam)
                    .map { case (sym, expr) => sym -> expr }
                    .toMap
              }

            val selectTpe = symbol.tpe match {
              case tpe: Type.RefType => tpe.replaceWithMap(hpTable, tpTable)
              case tpe: Type.MethodType => tpe.replaceWithMap(hpTable, tpTable)
              case Type.ErrorType => Type.ErrorType
            }

            select.copy(typedPrefix, select.name)
              .setTpe(selectTpe)
              .setSymbol(symbol)
              .setID(select.id)
        }
      case Type.ErrorType =>
        select.copy(typedPrefix, select.name)
          .setTpe(Type.ErrorType)
          .setSymbol(Symbol.ErrorSymbol)
          .setID(select.id)
    }
  }

  def typedFieldPair(
    targetTpe: Type.RefType,
    pair: ConstructPair,
    hpTable: Map[Symbol.HardwareParamSymbol, HPExpr],
    tpTable: Map[Symbol.TypeParamSymbol, Type.RefType]
  )(implicit ctx: Context.NodeContext, global: GlobalData): (Option[Error], ConstructPair) = {
    val typedInit = typedExpr(pair.init)
    val typedPair = pair.copy(init = typedInit).setID(pair.id)

    val err = targetTpe.lookupField(pair.name, ctx.hpBounds, ctx.tpBounds)(pair.position, global) match {
      case LookupResult.LookupFailure(err) => Some(err)
      case LookupResult.LookupSuccess(symbol) => (symbol.tpe, typedInit.tpe) match {
        case (Type.ErrorType, _) => Some(Error.DummyError)
        case (_, Type.ErrorType) => Some(Error.DummyError)
        case (fieldTpe: Type.RefType, exprTpe: Type.RefType) =>
          val replacedFieldTpe = fieldTpe.replaceWithMap(hpTable, tpTable)
          if (replacedFieldTpe == exprTpe) None
          else Some(Error.TypeMismatch(fieldTpe, exprTpe, pair.position))
      }
    }

    (err, typedPair)
  }

  def typedModulePair(
    targetTpe: Type.RefType,
    pair: ConstructPair,
    hpTable: Map[Symbol.HardwareParamSymbol, HPExpr],
    tpTable: Map[Symbol.TypeParamSymbol, Type.RefType]
  )(implicit ctx: Context.NodeContext, global: GlobalData): (Option[Error], ConstructPair) = {
    val (err, typedInit) = pair.init match {
      case ths: This => (None, typedThis(ths))
      case select @ Select(This(), _) => (None, typedExprSelect(select))
      case construct: ConstructClass => (None, typedConstructClass(construct))
      case construct: ConstructModule => (None, typedConstructModule(construct))
      case expr =>
        val err = Error.InvalidFormatForModuleConstruct(expr, expr.position)
        val typedExpr = expr match {
          case e: Expression with HasSymbol => e.setTpe(Type.ErrorType).setSymbol(Symbol.ErrorSymbol)
          case e => e.setTpe(Type.ErrorType)
        }

        (Some(err), typedExpr)
    }

    val typedPair = ConstructPair(pair.name, typedInit, pair.position).setID(pair.id)

    val pairErr = targetTpe.lookupField(pair.name, ctx.hpBounds, ctx.tpBounds)(pair.position, global) match {
      case LookupResult.LookupFailure(err) => Some(err)
      case LookupResult.LookupSuccess(symbol) => (symbol.tpe, typedInit.tpe) match {
        case (Type.ErrorType, _) => Some(Error.DummyError)
        case (_, Type.ErrorType) => Some(Error.DummyError)
        case (fieldTpe: Type.RefType, exprTpe: Type.RefType) =>
          val replacedFieldTpe = fieldTpe.replaceWithMap(hpTable, tpTable)
          if (replacedFieldTpe == exprTpe) None
          else Some(Error.TypeMismatch(fieldTpe, exprTpe, pair.position))
      }
    }

    val errs = Vector(err, pairErr).flatten
    val combinedErr =
      if (errs.isEmpty) None
      else Some(Error.MultipleErrors(errs: _*))

    (combinedErr, typedPair)
  }

  def typedMatch(matchExpr: Match)(implicit ctx: Context.NodeContext, global: GlobalData): Match = {
    def typedCase(caseDef: Case, matchedTpe: Type.RefType): Case = {
      val caseCtx = Context(ctx)
      typedPattern(caseDef.pattern, matchedTpe, caseCtx) match {
        case Left(err) =>
          global.repo.error.append(err)
          Case(caseDef.pattern, caseDef.exprs, caseDef.position).setTpe(Type.ErrorType).setID(caseDef.id)
        case Right(pattern) =>
          val blockElems = caseDef.exprs.map(typedBlockElem(_)(caseCtx, global))
          val (typedElems, retTpe) = blockElems.last match {
            case expr: Expression => (blockElems, expr.tpe)
            case _ =>
              val unitLit = UnitLiteral(Position.empty).setTpe(Type.unitTpe)
              (blockElems :+ unitLit, Type.unitTpe)
          }

          Case(pattern, typedElems, caseDef.position).setTpe(retTpe).setID(caseDef.id)
      }
    }

    def typedPattern(pattern: MatchPattern, matchedTpe: Type.RefType, ctx: Context.NodeContext): Either[Error, MatchPattern] = pattern match {
      case enum: EnumPattern => typedEnumPattern(enum, matchedTpe, ctx, pattern.position)
      case ident: IdentPattern => typedIdentPattern(ident, matchedTpe, ctx)
      case lit: LiteralPattern => typedLiteralPattern(lit, matchedTpe)
      case wild: WildCardPattern => Right(WildCardPattern(wild.position).setTpe(matchedTpe).setID(wild.id))
    }

    def typedIdentPattern(pattern: IdentPattern, matchedTpe: Type.RefType, ctx: Context.NodeContext): Either[Error, IdentPattern] = {
      val symbol = Symbol.VariableSymbol.local(
        pattern.ident.name,
        ctx.path,
        Accessibility.Private,
        Modifier.Local,
        matchedTpe
      )

      ctx.append(symbol)
      val ident = pattern.ident.setSymbol(symbol).setTpe(matchedTpe)
      Right(IdentPattern(ident, pattern.position))
    }

    def typedLiteralPattern(pattern: LiteralPattern, matchedTpe: Type.RefType): Either[Error, LiteralPattern] = {
      val result = pattern.lit match {
        case lit: IntLiteral =>
          if(Type.intTpe == matchedTpe) Right(lit.setTpe(Type.intTpe))
          else Left(Error.TypeMismatch(matchedTpe, Type.intTpe, lit.position))
        case lit @ BitLiteral(_, length) =>
          if(Type.bitTpe(length) == matchedTpe) Right(lit.setTpe(Type.bitTpe(length)))
          else Left(Error.TypeMismatch(matchedTpe, Type.bitTpe(length), lit.position))
        case lit: BoolLiteral =>
          if(Type.boolTpe == matchedTpe) Right(lit.setTpe(Type.boolTpe))
          else Left(Error.TypeMismatch(matchedTpe, Type.boolTpe, lit.position))
        case lit: UnitLiteral =>
          if(Type.unitTpe == matchedTpe) Right(lit.setTpe(Type.unitTpe))
          else Left(Error.TypeMismatch(matchedTpe, Type.unitTpe, lit.position))
      }

      result.map(LiteralPattern(_, pattern.position))
    }

    def typedEnumPattern(enum: EnumPattern, matchedTpe: Type.RefType, ctx: Context.NodeContext, position: Position): Either[Error, EnumPattern] = {
      val typedVariant = typedTypeTree(enum.variant)(ctx, global)
      def requireRefType(tpe: Type): Either[Error, Type.RefType] = tpe match {
        case tpe: Type.RefType => Right(tpe)
        case Type.ErrorType => Left(Error.DummyError)
      }

      def requireSameEnumType(tpe: Type.RefType, pos: Position): Either[Error, Unit] =
        if(tpe == matchedTpe) Right(())
        else Left(Error.TypeMismatch(matchedTpe, tpe, pos))

      def requireEnumVariant(symbol: Symbol, pos: Position): Either[Error, Symbol.EnumMemberSymbol] = symbol match {
        case Symbol.ErrorSymbol => Left(Error.DummyError)
        case symbol: Symbol.EnumMemberSymbol => Right(symbol)
        case symbol => Left(Error.RequireSymbol[Symbol.EnumMemberSymbol](symbol, pos))
      }

      def verifyFieldLength(symbol: Symbol.EnumMemberSymbol, pos: Position): Either[Error, Unit] = {
        val tpe = symbol.tpe.asEnumMemberType
        val expect = tpe.fields.length
        val actual = enum.patterns.length

        if(expect == actual) Right(())
        else Left(Error.PatternLengthMismatch(symbol, expect, actual, pos))
      }

      def typedPatterns(fieldTpes: Vector[Type.RefType]): Either[Error, Vector[MatchPattern]] = {
        val (errs, patterns) = (enum.patterns zip fieldTpes)
          .map{ case (pattern, tpe) => typedPattern(pattern, tpe, ctx) }
          .partitionMap(identity)

        if(errs.isEmpty) Right(patterns)
        else Left(Error.MultipleErrors(errs: _*))
      }

      val hpTable = (matchedTpe.origin.hps zip matchedTpe.hardwareParam).toMap
      val tpTable = (matchedTpe.origin.tps zip matchedTpe.typeParam).toMap

      for {
        tpe <- requireRefType(typedVariant.tpe)
        _ <- requireSameEnumType(tpe, typedVariant.position)
        variant <- requireEnumVariant(typedVariant.symbol, typedVariant.position)
        _ <- verifyFieldLength(variant, typedVariant.position)
        variantFields = variant.tpe.asEnumMemberType.fields
        fieldTpes = variantFields.map(_.tpe.asRefType.replaceWithMap(hpTable, tpTable))
        patterns <- typedPatterns(fieldTpes)
      } yield EnumPattern(typedVariant, patterns, matchExpr.position)
    }

    val Match(matched, cases) = matchExpr
    val typedMatched = typedExpr(matched)

    typedMatched.tpe match {
      case Type.ErrorType => Match(typedMatched, cases, matchExpr.position).setTpe(Type.ErrorType).setID(matchExpr.id)
      case tpe: Type.RefType =>
        val typedCases = cases.map(typedCase(_, tpe))

        def hasError: Either[Error, Unit] =
          if (typedCases.map(_.tpe).exists(_.isErrorType)) Left(Error.DummyError)
          else Right(())

        def typeMismatches: Either[Error, Unit] = {
          val retTpes = typedCases.map(_.tpe.asRefType)
          val caseErrs = typedCases.filterNot(_.tpe.isErrorType)
            .filter(_.tpe.asRefType != retTpes.last)
            .map(c => Error.TypeMismatch(retTpes.last, c.tpe, c.position))

          if (caseErrs.isEmpty) Right(())
          else Left(Error.MultipleErrors(caseErrs: _*))
        }

        def requireSizedType: Either[Error, Unit] = {
          val tpe = typedCases.head.tpe.asRefType
          val isHardwareType = tpe.isHardwareType(ctx.tpBounds)(typedCases.head.position, global)
          val isPointer = tpe.isPointer

          if(isHardwareType || isPointer) Right(())
          else Left(Error.RequirePointerOrHWType(tpe, typedMatched.position))
        }

        val result = for {
          _ <- hasError
          _ <- typeMismatches
          _ <- requireSizedType
        } yield Match(typedMatched, typedCases, matchExpr.position)
          .setTpe(typedCases.head.tpe)
          .setID(matchExpr.id)

        result match {
          case Right(matchExpr) => matchExpr
          case Left(err) =>
            global.repo.error.append(err)
            Match(typedMatched, typedCases, matchExpr.position)
              .setTpe(Type.ErrorType)
              .setID(matchExpr.id)
        }
    }
  }

  def typedConstructClass(construct: ConstructClass)(implicit ctx: Context.NodeContext, global: GlobalData): Construct = {
    val typedTarget = typedTypeTree(construct.target)

    typedTarget.tpe match {
      case Type.ErrorType => construct.copy(target = typedTarget).setTpe(Type.ErrorType).setID(construct.id)
      case tpe: Type.RefType =>
        val hpTable = (tpe.origin.hps zip tpe.hardwareParam).toMap
        val tpTable = (tpe.origin.tps zip tpe.typeParam).toMap
        val (errOpts, typedPairs) = construct.fields.map(typedFieldPair(tpe, _, hpTable, tpTable)).unzip
        val errs = errOpts.flatten

        errs.foreach(global.repo.error.append)

        tpe.origin match {
          case _: Symbol.StructSymbol =>
            ConstructClass(typedTarget, typedPairs, construct.position)
              .setSymbol(typedTarget.symbol)
              .setTpe(tpe)
              .setID(construct.id)
          case _: Symbol.ModuleSymbol if construct.fields.isEmpty =>
            ConstructModule(typedTarget, Vector.empty, Vector.empty, construct.position)
              .setSymbol(typedTarget.symbol)
              .setTpe(tpe)
              .setID(construct.id)
          case _: Symbol.ModuleSymbol =>
            global.repo.error.append(Error.RequireParentOrSiblingIndicator(construct, construct.position))
            ConstructClass(typedTarget, typedPairs, construct.position)
              .setSymbol(Symbol.ErrorSymbol)
              .setTpe(Type.ErrorType)
              .setID(construct.id)
          case _: Symbol.InterfaceSymbol =>
            global.repo.error.append(Error.TryToConstructInterface(construct, construct.position))
            ConstructClass(typedTarget, typedPairs, construct.position)
              .setSymbol(Symbol.ErrorSymbol)
              .setTpe(Type.ErrorType)
              .setID(construct.id)
        }
    }
  }

  def typedConstructModule(construct: ConstructModule)(implicit ctx: Context.NodeContext, global: GlobalData): ConstructModule = {
    val typedTarget = typedTypeTree(construct.target)

    typedTarget.tpe match {
      case Type.ErrorType => construct.copy(target = typedTarget).setTpe(Type.ErrorType).setID(construct.id)
      case tpe: Type.RefType =>
        val hpTable = (tpe.origin.hps zip tpe.hardwareParam).toMap
        val tpTable = (tpe.origin.tps zip tpe.typeParam).toMap
        val (errOpts0, typedParents) = construct.parents.map(typedFieldPair(tpe, _, hpTable, tpTable)).unzip
        val (errOpts1, typedSiblings) = construct.siblings.map(typedFieldPair(tpe, _, hpTable, tpTable)).unzip

        (errOpts0 ++ errOpts1).flatten.foreach(global.repo.error.append)

        val returnType = tpe.origin match {
          case _: Symbol.ModuleSymbol => tpe
          case _: Symbol.StructSymbol =>
            global.repo.error.append(Error.RejectParentOrSiblingIndicator(construct, construct.target.position))
            Type.ErrorType
          case _: Symbol.InterfaceSymbol =>
            global.repo.error.append(Error.TryToConstructInterface(construct, construct.target.position))
            Type.ErrorType
        }

        ConstructModule(typedTarget, typedParents, typedSiblings, construct.position)
          .setSymbol(typedTarget.symbol)
          .setTpe(returnType)
          .setID(construct.id)
    }
  }

  def typedConstructEnum(construct: ConstructEnum)(implicit ctx: Context.NodeContext, global: GlobalData): ConstructEnum = {
    def verifyFields(parent: Type.RefType, target: Symbol.EnumMemberSymbol, fields: Vector[Expression]): Either[Error, Unit] = {
      val tpe = target.tpe.asEnumMemberType
      val declares = tpe.declares.toMap.toVector.sortWith {
        case ((left, _), (right, _)) => left < right
      }

      def verifyLength =
        if (declares.length == fields.length) Right(())
        else Left(Error.ParameterLengthMismatch(declares.length, fields.length, construct.position))

      def verifyFieldExprType =
        if (fields.exists(_.tpe.isErrorType)) Left(Error.DummyError)
        else Right(())

      def typeMismatches(
        hpTable: Map[Symbol.HardwareParamSymbol, HPExpr],
        tpTable: Map[Symbol.TypeParamSymbol, Type.RefType]
      ): Vector[Error.TypeMismatch] = {
        val expectTpes = declares
          .map { case (_, symbol) => symbol }
          .map(_.tpe.asRefType)
          .map(_.replaceWithMap(hpTable, tpTable))

        (expectTpes zip fields)
            .filterNot { case (_, expr) => expr.tpe.isErrorType }
            .filter { case (field, expr) => field != expr.tpe }
            .map { case (field, expr) => Error.TypeMismatch(field, expr.tpe.asRefType, expr.position) }
      }

      def verifyTypeMatching: Either[Error, Unit] = {
        val hpTable = (parent.origin.hps zip parent.hardwareParam).toMap
        val tpTable = (parent.origin.tps zip parent.typeParam).toMap

        val mismatches = typeMismatches(hpTable, tpTable)

        if (mismatches.isEmpty) Right(())
        else Left(Error.MultipleErrors(mismatches: _*))
      }

      for {
        _ <- verifyLength
        _ <- verifyFieldExprType
        _ <- verifyTypeMatching
      } yield ()
    }

    val typedTarget = typedTypeTree(construct.target)
    val typedFields = construct.fields.map(typedExpr)

    val result = typedTarget.symbol match {
      case member: Symbol.EnumMemberSymbol =>
        verifyFields(typedTarget.tpe.asRefType, member, typedFields)
          .map(_ => typedTarget.tpe.asRefType)
      case _ => typedTarget.tpe match {
        case tpe: Type.RefType => Left(Error.ConstructEnumForm(tpe, typedTarget.position))
        case Type.ErrorType => Left(Error.DummyError)
      }
    }

    val tpe = result match {
      case Right(tpe) => tpe
      case Left(err) =>
        global.repo.error.append(err)
        Type.ErrorType
    }

    ConstructEnum(typedTarget, typedFields, construct.position)
      .setSymbol(typedTarget.symbol)
      .setTpe(tpe)
      .setID(construct.id)
  }

  def typedCastExpr(cast: CastExpr)(implicit ctx: Context.NodeContext, global: GlobalData): CastExpr = {
    def verifyType(tpe: AST with HasType): Either[Error, Type.RefType] = {
      tpe.tpe match {
        case Type.ErrorType => Left(Error.DummyError)
        case tpe: Type.RefType => Right(tpe)
      }
    }

    val typedPrefix = typedExpr(cast.expr)
    val typedTpeTree = typedTypeTree(cast.to)

    val result = for {
      from <- verifyType(typedPrefix)
      to <- verifyType(typedTpeTree)
      castTpe <- castVerification(from, to, cast.position, cast.expr.position, cast.to.position)
    } yield castTpe

    val tpe = result match {
      case Right(tpe) => tpe
      case Left(err) =>
        global.repo.error.append(err)
        Type.ErrorType
    }

    CastExpr(typedPrefix, typedTpeTree, cast.position).setTpe(tpe).setID(cast.id)
  }


  def typedStdBinOp(binop: StdBinOp)(implicit ctx: Context.NodeContext, global: GlobalData): StdBinOp = {
    val typedLeft = typedExpr(binop.left)
    val typedRight = typedExpr(binop.right)

    val result = (typedLeft.tpe, typedRight.tpe) match {
      case (Type.ErrorType, _) => LookupResult.LookupFailure(Error.DummyError)
      case (_, Type.ErrorType) => LookupResult.LookupFailure(Error.DummyError)
      case (leftTpe: Type.RefType, rightTpe: Type.RefType) =>
        leftTpe.lookupOperator(binop.op, Vector(leftTpe, rightTpe), ctx.hpBounds, ctx.tpBounds, binop.position)
    }

    result match {
      case LookupResult.LookupFailure(err) =>
        global.repo.error.append(err)
        binop.setSymbol(Symbol.ErrorSymbol).setTpe(Type.ErrorType)
      case LookupResult.LookupSuccess((methodSymbol, methodTpe)) =>
        StdBinOp(binop.op, typedLeft, typedRight, binop.position)
          .setSymbol(methodSymbol)
          .setTpe(methodTpe.returnType)
          .setID(binop.id)
    }
  }

  def typedStdUnaryOp(unaryOp: StdUnaryOp)(implicit ctx: Context.NodeContext, global: GlobalData): StdUnaryOp = {
    val typedOperand = typedExpr(unaryOp.operand)

    val result = typedOperand.tpe match {
      case Type.ErrorType => LookupResult.LookupFailure(Error.DummyError)
      case operand: Type.RefType => operand.lookupOperator(unaryOp.op, Vector(operand), ctx.hpBounds, ctx.tpBounds,typedOperand.position)
    }

    result match {
      case LookupResult.LookupFailure(err) =>
        global.repo.error.append(err)
        unaryOp.setSymbol(Symbol.ErrorSymbol).setTpe(Type.ErrorType)
      case LookupResult.LookupSuccess((symbol, tpe)) =>
        unaryOp.copy(operand = typedOperand).setSymbol(symbol).setTpe(tpe.returnType)
    }
  }

  def typedDeReference(deref: DeReference)(implicit ctx: Context.NodeContext, global: GlobalData): DeReference = {
    val expr = typedExpr(deref.expr)
    val result = expr.tpe match {
      case Type.ErrorType => Left(Error.DummyError)
      case tpe: Type.RefType if !tpe.isPointer => Left(Error.RequirePointerType(tpe, deref.position))
      case tpe: Type.RefType =>
        val refTpe = Type.RefType(tpe.origin, tpe.hardwareParam, tpe.typeParam, isPointer = false)
        Right(refTpe)
    }

    result match {
      case Right(tpe) => deref.copy(expr = expr).setTpe(tpe)
      case Left(err) =>
        global.repo.error.append(err)
        deref.copy(expr = expr).setTpe(Type.ErrorType)
    }
  }


  def typedBlock(blk: Block)(implicit ctx: Context.NodeContext, global: GlobalData): Block = {
    val blkCtx = Context.blk(ctx)
    val typedElems = blk.elems.map(typedBlockElem(_)(blkCtx, global))
    val typedLast = typedExpr(blk.last)(blkCtx, global)

    Block(typedElems, typedLast, blk.position).setTpe(typedLast.tpe).setID(blk.id)
  }

  def typedBlockElem(elem: BlockElem)(implicit ctx: Context.NodeContext, global: GlobalData): BlockElem =
    elem match {
      case vdef: ValDef => typedExprValDef(vdef)
      case assign: Assign => typedAssign(assign)
      case expr: Expression => typedExpr(expr)
    }

  def typedThis(self: This)(implicit ctx: Context.NodeContext, global: GlobalData): This = {
    val tpe = ctx.self match {
      case None =>
        global.repo.error.append(Error.UsingSelfOutsideClass(self.position))
        Type.ErrorType
      case Some(_) if ctx.isStatic =>
        global.repo.error.append(Error.UsingSelfInsideStatic(self.position))
        Type.ErrorType
      case Some(tpe) =>
        tpe
    }

    This(self.position).setTpe(tpe).setID(self.id)
  }

  def typedAssign(assign: Assign)(implicit ctx: Context.NodeContext, global: GlobalData): Assign = {
    val Assign(loc, expr) = assign
    val typedRhs = typedExpr(expr)

    def verifyTreeForm: Either[Error, (Expression, String)] = loc match {
      case Select(prefix, name) => prefix match {
        case self: This => Right(typedThis(self), name)
        case select @ Select(_: This, _) => Right(typedExprSelect(select), name)
        case tree => Left(Error.InvalidLHSForm(tree, assign.right.position))
      }
      case tree => Left(Error.InvalidLHSForm(tree, assign.right.position))
    }

    def rejectErrorType(prefix: Expression): Either[Error, Type.RefType] = prefix.tpe match {
      case Type.ErrorType => Left(Error.DummyError)
      case tpe: Type.RefType => Right(tpe)
    }

    def requireModuleType(prefix: Type.RefType, position: Position): Either[Error, Unit] = prefix.origin match {
      case _: Symbol.ModuleSymbol => Right(())
      case symbol => Left(Error.RequireSymbol[Symbol.ModuleSymbol](symbol, position))
    }

    def typeCheck(ltype: Type, rtype: Type): Either[Error, Unit] = {
      (ltype, rtype) match {
        case (l: Type.RefType, r: Type.RefType) if l != r => Left(Error.TypeMismatch(l, r, assign.position))
        case _ => Right(())
      }
    }

    val typedLoc = for {
      pair <- verifyTreeForm
      (prefixTree, name) = pair
      prefixTpe <- rejectErrorType(prefixTree)
      _ <- requireModuleType(prefixTpe, prefixTree.position)
      symbol <- prefixTpe.lookupField(name, ctx.hpBounds, ctx.tpBounds)(prefixTree.position, global).toEither
    } yield Select(prefixTree, name, loc.position)
      .setSymbol(symbol)
      .setTpe(symbol.tpe)
      .setID(loc.id)

    typedLoc.left.foreach(global.repo.error.append)
    typedLoc.foreach(loc => typeCheck(loc.tpe, typedRhs.tpe).left.foreach(global.repo.error.append))
    Assign(typedLoc.getOrElse(loc), typedRhs, assign.position).setID(assign.id)
  }

  def typedIfExpr(ifexpr: IfExpr)(implicit ctx: Context.NodeContext, global: GlobalData): IfExpr = {
    val typedCond = typedExpr(ifexpr.cond)
    val typedConseq = typedExpr(ifexpr.conseq)
    val typedAlt = ifexpr.alt.map(typedExpr)

    def isBoolTpe = typedCond.tpe =:= Type.boolTpe
    def isErrorTpe = typedCond.tpe.isErrorType

    if (!isErrorTpe && !isBoolTpe)
      global.repo.error.append(Error.RequireSpecificType(typedCond.tpe.asRefType, Seq(Type.boolTpe), ifexpr.cond.position))

    typedAlt match {
      case None =>
        IfExpr(typedCond, typedConseq, typedAlt, ifexpr.position).setTpe(Type.unitTpe).setID(ifexpr.id)
      case Some(alt) =>
        val retTpe = (alt.tpe, typedConseq.tpe) match {
          case (Type.ErrorType, tpe) => tpe
          case (tpe, Type.ErrorType) => tpe
          case (altTpe: Type.RefType, conseqTpe: Type.RefType) =>
            if (altTpe != conseqTpe)
              global.repo.error.append(Error.TypeMismatch(altTpe, conseqTpe, ifexpr.cond.position))

            val isHWType = altTpe.isHardwareType(ctx.tpBounds)(ifexpr.cond.position, global)
            val isPointerHWType = altTpe.isPointer
            if (!isHWType && !isPointerHWType)
              global.repo.error.append(Error.RequirePointerOrHWType(altTpe, ifexpr.cond.position))

            altTpe
        }


        IfExpr(typedCond, typedConseq, typedAlt, ifexpr.position).setTpe(retTpe).setID(ifexpr.id)
    }
  }

  def typedTypeTree(typeTree: TypeTree)(implicit ctx: Context.NodeContext, global: GlobalData): TypeTree = {
    def verifyHP(symbol: Symbol.TypeSymbol, typedHPs: Vector[HPExpr]): Either[Error, Unit] = {
      val invalidHPLength = symbol.hps.length != typedHPs.length
      val hasError = typedHPs.exists(_.tpe.isErrorType)

      if (invalidHPLength) Left(Error.HardParameterLengthMismatch(symbol.hps.length, typeTree.hp.length, typeTree.position))
      else if (hasError) Left(Error.DummyError)
      else {
        val table = (symbol.hps zip typedHPs).toMap
        val swapped = HPBound.swapBounds(symbol.hpBound, table)

        val (errs, _) = swapped
          .map(HPBound.verifyMeetBound(_, ctx.hpBounds))
          .partitionMap(identity)

        if (errs.isEmpty) Right(())
        else Left(Error.MultipleErrors(errs: _*))
      }
    }

    def verifyTP(symbol: Symbol.TypeSymbol, typedHPs: Vector[HPExpr], typedTPs: Vector[TypeTree]): Either[Error, Unit] = {
      val invalidTPLength = symbol.tps.length != typedTPs.length
      lazy val hasError = typedTPs.exists(_.tpe.isErrorType)
      lazy val tpRefTpe = typedTPs.map(_.tpe.asRefType)

      if (invalidTPLength) Left(Error.TypeParameterLengthMismatch(symbol.tps.length, typedTPs.length, typeTree.position))
      else if (hasError) Left(Error.DummyError)
      else {
        val hpTable = (symbol.hps zip typedHPs).toMap
        val tpTable = (symbol.tps zip tpRefTpe).toMap
        val swapped = TPBound.swapBounds(symbol.tpBound, hpTable, tpTable)
        val (errs, _) = swapped
          .map(TPBound.verifyMeetBound(_, ctx.hpBounds, ctx.tpBounds, typeTree.position))
          .partitionMap(identity)

        if (errs.isEmpty) Right(())
        else Left(Error.MultipleErrors(errs: _*))
      }
    }

    def typedForIdent(ident: Ident, hargs: Vector[HPExpr], targs: Vector[TypeTree]): Either[Error, TypeTree] =
      ctx.lookup[Symbol.TypeSymbol](ident.name) match {
        case LookupResult.LookupFailure(err) => Left(err)
        case LookupResult.LookupSuccess(_: Symbol.EnumMemberSymbol) =>
          throw new ImplementationErrorException("using enum member name directly to construct enum value is not supported yet")
        case LookupResult.LookupSuccess(symbol) =>
          for {
            _ <- verifyHP(symbol, hargs)
            _ <- verifyTP(symbol, hargs, targs)
          } yield {
            val tpe = Type.RefType(symbol, hargs, targs.map(_.tpe.asRefType), isPointer = false)

            TypeTree(ident.setTpe(symbol.tpe).setSymbol(symbol), hargs, targs, isPointer = false, typeTree.position)
              .setTpe(tpe)
              .setSymbol(symbol)
              .setID(typeTree.id)
          }
      }

    def typedForCast(cast: CastType): Either[Error, TypeTree] = {
      def checkType(tpe: TypeTree): Either[Error, Type.RefType] =
        if (tpe.tpe.isErrorType) Left(Error.DummyError)
        else Right(tpe.tpe.asRefType)

      val CastType(from, to) = cast

      val typedFrom = typedTypeTree(from)
      val typedTo = typedTypeTree(to)

      for {
        fromTpe <- checkType(typedFrom)
        toTpe <- checkType(typedTo)
        castTpe <- castVerification(fromTpe, toTpe, cast.position, cast.from.position, cast.to.position)
      } yield {
        val typedCast = CastType(typedFrom, typedTo, cast.position)
          .setTpe(castTpe)
          .setSymbol(castTpe.origin)
          .setID(cast.id)

        TypeTree(typedCast, Vector.empty, Vector.empty, isPointer = false, typeTree.position)
          .setTpe(castTpe)
          .setSymbol(castTpe.origin)
          .setID(cast.id)
      }
    }

    def typedForStaticSelect(select: StaticSelect, hargs: Vector[HPExpr], targs: Vector[TypeTree]): Either[Error, TypeTree] = {
      def typedPrefix: Either[Error, TypeTree] = {
        val tree = typedTypeTree(select.prefix)

        tree.tpe match {
          case Type.ErrorType => Left(Error.DummyError)
          case _ => Right(tree)
        }
      }

      val result = for {
        prefix <- typedPrefix
        symbol <- prefix.tpe.asRefType.lookupType(select.name)(select.position).toEither
        _ <- verifyHP(symbol, hargs)
        _ <- verifyTP(symbol, hargs, targs)
      } yield (prefix, symbol)

      result match {
        case Left(err) => Left(err)
        case Right(pair @ (prefixTree, _)) =>
          val (symbol, tpe) = pair match {
            case (prefix, symbol: Symbol.EnumMemberSymbol) => (symbol, prefix.tpe)
            case (_, symbol) => (symbol, Type.RefType.accessed(prefixTree.tpe.asRefType, symbol.tpe.asRefType, symbol.tpe.asRefType.isPointer))
          }

          val typedSelect = StaticSelect(prefixTree, select.name, select.position)
            .setSymbol(symbol)
            .setTpe(tpe)
            .setID(select.id)

          Right(TypeTree(typedSelect, hargs, targs, isPointer = false, typeTree.position).setTpe(tpe).setSymbol(symbol).setID(typeTree.id))
      }
    }

    def typedForSelectPackage(select: SelectPackage, hargs: Vector[HPExpr], targs: Vector[TypeTree]): Either[Error, TypeTree] = {
      def lookupPackageFromCtx: Either[Error, Symbol.PackageSymbol] = {
        val head = ctx.lookup[Symbol.PackageSymbol](select.packages.head).toEither

        select.packages.tail.foldLeft(head) {
          case (Left(err), _) => Left(err)
          case (Right(symbol), name) => symbol.lookup[Symbol.PackageSymbol](name).toEither
        }
      }

      def lookupPackageFromRoot: Either[Error, Symbol.PackageSymbol] = global.rootPackage.search(select.packages)

      for {
        packageSymbol <- lookupPackageFromCtx.flatMap(_ => lookupPackageFromRoot)
        typeSymbol <- packageSymbol.lookup[Symbol.TypeSymbol](select.name).toEither
        _ <- verifyHP(typeSymbol, hargs)
        _ <- verifyTP(typeSymbol, hargs, targs)
      } yield {
        val typedSelect = select.setSymbol(typeSymbol).setTpe(typeSymbol.tpe)
        val tpe = Type.RefType(typeSymbol, hargs, targs.map(_.tpe.asRefType), isPointer = false)

        TypeTree(typedSelect, hargs, targs, isPointer = false, typeTree.position)
          .setSymbol(typeSymbol)
          .setTpe(tpe)
          .setID(typeTree.id)
      }
    }

    def typedForThisType(thisTree: ThisType): Either[Error, TypeTree] =
      ctx.self match {
        case None => Left(Error.SelfTypeNotFound(thisTree.position))
        case Some(tpe) =>
          val tree = ThisType(thisTree.position).setSymbol(tpe.origin).setTpe(tpe).setID(thisTree.id)
          val tpeTree = TypeTree(tree, Vector.empty, Vector.empty, isPointer = false, thisTree.position)
            .setSymbol(tree.symbol)
            .setTpe(tree.tpe)

          Right(tpeTree)
      }

    def execTyped(hargs: Vector[HPExpr], targs: Vector[TypeTree]): Either[Error, TypeTree] = {
      def exec: Either[Error, TypeTree] =
        typeTree.expr match {
          case ident: Ident => typedForIdent(ident, hargs, targs)
          case cast: CastType => typedForCast(cast)
          case select: StaticSelect => typedForStaticSelect(select, hargs, targs)
          case select: SelectPackage => typedForSelectPackage(select, hargs, targs)
          case tree: ThisType => typedForThisType(tree)
        }

      def pointerVerify(typedTree: TypeTree): Either[Error, Type.RefType] = {
        // Don't use typedTree.isPointer as condition because typedTree.isPointer must be false.
        // typedTree.isPointer is assigned at post process after returning this inner method.
        if(!typeTree.isPointer) Right(typedTree.tpe.asRefType)
        else {
          // Add pointer flag here
          // because procedures before here does not care about whether the type is pointer or not.
          // That's why check here and Add pointer flag if so.
          val isHW = typedTree.tpe.asRefType.isHardwareType(ctx.tpBounds)(typeTree.position, global)
          val tpe = typedTree.tpe.asRefType
          val pointerTpe = Type.RefType(
            tpe.origin,
            tpe.hardwareParam,
            tpe.typeParam,
            isPointer = true
          )

          if(isHW) Right(pointerTpe)
          else Left(Error.RequireHWAsPointer(tpe, typedTree.position))
        }
      }

      for {
        tree <- exec
        tpe <- pointerVerify(tree)
      } yield tree.setTpe(tpe)
    }

    val typedHArgs = typeTree.hp.map(typedHPExpr)
    val typedTArgs = typeTree.tp.map(typedTypeTree)

    execTyped(typedHArgs, typedTArgs) match {
      case Right(tree) => tree.copy(isPointer = typeTree.isPointer)
      case Left(err) =>
        global.repo.error.append(err)
        val prefix = typeTree.expr.setTpe(Type.ErrorType).setSymbol(Symbol.ErrorSymbol)

        TypeTree(prefix, typedHArgs, typedTArgs, typeTree.isPointer, typeTree.position)
          .setTpe(Type.ErrorType)
          .setSymbol(Symbol.ErrorSymbol)
          .setID(typeTree.id)
    }
  }

  private def castVerification(from: Type.RefType, to: Type.RefType, castPos: Position, fromPos: Position, toPos: Position)(implicit ctx: Context.NodeContext, global: GlobalData): Either[Error, Type.RefType] = {
    def verifyFromType(tpe: Type.RefType): Either[Error, Unit] =
      if (tpe.origin.isInterfaceSymbol) Left(Error.MustNotCastFromTrait(tpe, fromPos))
      else Right(())

    def verifyToType(tpe: Type.RefType): Either[Error, Unit] =
      if (tpe.origin.isInterfaceSymbol) Right(())
      else Left(Error.MustCastToTrait(tpe, toPos))

    def verifyCastable(from: Type.RefType, to: Type.RefType): Either[Error, Unit] = {
      val isCastable = from.origin match {
        case _: Symbol.TypeParamSymbol =>
          val bounds = ctx.tpBounds
            .find(_.target == from)
            .map(_.bounds)
            .getOrElse(Vector.empty)

          bounds.contains(to)
        case _: Symbol.ClassTypeSymbol =>
          to.origin.asInterfaceSymbol.impls.exists {
            impl =>
              val targets = Vector(impl.targetType, impl.targetInterface)
              val callers = Vector(from, to)
              val positions = Vector(fromPos, toPos)

              Type.RefType.verifySuperSets(callers, targets, positions).isRight
          }
      }

      if (isCastable) Right(())
      else Left(Error.CannotCast(from, to, castPos))
    }

    for {
      _ <- verifyFromType(from)
      _ <- verifyToType(to)
      _ <- verifyCastable(from, to)
    } yield Type.RefType.cast(from, to)
  }

  def typedBitLiteral(bit: BitLiteral)(implicit ctx: Context.NodeContext, global: GlobalData): BitLiteral = {
    val length = IntLiteral(bit.length, Position.empty).setTpe(Type.numTpe)
    val bitTpe = Type.bitTpe(length)

    bit.setTpe(bitTpe).setID(bit.id)
  }

  def typedIntLiteral(int: IntLiteral)(implicit ctx: Context.NodeContext, global: GlobalData): IntLiteral = {
    int.setTpe(Type.intTpe)
  }

  def typedBoolLiteral(bool: BoolLiteral)(implicit ctx: Context.NodeContext, global: GlobalData): BoolLiteral = {
    bool.setTpe(Type.boolTpe)
  }

  def typedUnitLiteral(unit: UnitLiteral)(implicit ctx: Context.NodeContext, global: GlobalData): UnitLiteral = {
    unit.setTpe(Type.unitTpe).setID(unit.id)
  }

  def typedFinish(finish: Finish)(implicit ctx: Context.NodeContext, global: GlobalData): Finish = {
    ctx.owner match {
      case _: Symbol.StateSymbol =>
      case _: Symbol.StageSymbol =>
      case _ => global.repo.error.append(Error.FinishOutsideStage(finish.position))
    }

    finish.setTpe(Type.unitTpe).setID(finish.id)
  }

  def typedGoto(goto: Goto)(implicit ctx: Context.NodeContext, global: GlobalData): Goto = {
    val typedArgs = goto.args.map(typedExpr)
    val symbol = ctx.owner match {
      case _: Symbol.StateSymbol =>
        ctx.lookup[Symbol.StateSymbol](goto.target) match {
          case LookupResult.LookupSuccess(symbol) => symbol
          case LookupResult.LookupFailure(err) =>
            global.repo.error.append(err)
            Symbol.ErrorSymbol
        }
      case _ =>
        global.repo.error.append(Error.GotoOutsideState(goto.position))
        Symbol.ErrorSymbol
    }

    val result = symbol.tpe match {
      case Type.ErrorType => Left(Error.DummyError)
      case tpe: Type.MethodType =>
        lazy val lengthMismatch: Either[Error, Unit] =
          if (tpe.params.length == typedArgs.length) Right(())
          else Left(Error.ParameterLengthMismatch(tpe.params.length, typedArgs.length, goto.position))

        lazy val typeMismatches: Either[Error, Unit] =
          (tpe.params zip typedArgs)
            .collect { case (param: Type.RefType, arg) => param -> arg }
            .filterNot { case (_, arg) => arg.tpe.isErrorType }
            .filter { case (param, arg) => param != arg.tpe.asRefType }
            .map { case (param, arg) => Error.TypeMismatch(param, arg.tpe.asRefType, arg.position) }
            .combine(errs => Error.MultipleErrors(errs: _*))

        for {
          _ <- lengthMismatch
          _ <- typeMismatches
        } yield ()
    }


    val stateSymbol = result match {
      case Right(_) => symbol
      case Left(err) =>
        global.repo.error.append(err)
        Symbol.ErrorSymbol
    }

    goto.copy(args = typedArgs).setSymbol(stateSymbol).setTpe(Type.unitTpe)
  }

  def typedCommence(commence: Commence)(implicit ctx: Context.NodeContext, global: GlobalData): Commence = {
    def verifyCallBlock(proc: ProcResult, args: Vector[Expression]): Either[Error, Symbol.ProcBlockSymbol] = {
      val target = commence.block.target
      proc.proc.tpe.declares.lookup(target) match {
        case None      => Left(Error.SymbolNotFound(target, commence.block.position))
        case Some(blk: Symbol.ProcBlockSymbol) =>
          val tpe = blk.tpe.asMethodType.replaceWithMap(proc.hpTable, proc.tpTable)
          val params = tpe.params

          if(args.length != params.length)
            return Left(Error.ParameterLengthMismatch(params.length, args.length, commence.block.position))

          val errs = (params zip args)
            .filter { case (p, a) => p != a.tpe }
            .map { case (p, a) => Error.TypeMismatch(p, a.tpe, a.position) }

          val notOriginErr =
            if(blk.flag.hasFlag(Modifier.Origin)) None
            else Some(Error.CommenceFromNonOrigin(blk, commence.block.position))

          (errs ++ notOriginErr).combine(errs => Error.MultipleErrors(errs: _*)).map(_ => blk)
        case Some(_) => Left(Error.SymbolNotFound(commence.block.target, commence.block.position))
      }
    }

    val self = ctx.self.getOrElse(throw new ImplementationErrorException("proc must be in module instance"))
    val typedArgs = commence.block.args.map(typedExpr)
    val hasError = typedArgs.exists(_.tpe.isErrorType)

    val result = self.lookupProc(commence.proc, ctx.hpBounds, ctx.tpBounds)(commence.position, global) match {
      case LookupResult.LookupFailure(err) => Left(err)
      case LookupResult.LookupSuccess(_) if hasError => Left(Error.DummyError)
      case LookupResult.LookupSuccess(result) => verifyCallBlock(result, typedArgs) match {
        case Left(err) => Left(err)
        case Right(blk) =>
          val typedBlk = commence.block.copy(args = typedArgs).setSymbol(blk)
          val typedCommence = commence.copy(block = typedBlk).setSymbol(result.proc).setTpe(result.retTpe)
          Right(typedCommence)
      }
    }

    result match {
      case Right(commence) => commence
      case Left(err) =>
        global.repo.error.append(err)
        commence.setSymbol(Symbol.ErrorSymbol).setTpe(Type.ErrorType)
    }
  }

  def typedGenerate(generate: Generate)(implicit ctx: Context.NodeContext, global: GlobalData): Generate = {
    val self = ctx.self.getOrElse(throw new ImplementationErrorException("stage must be in module instance"))
    val typedArgs = generate.args.map(typedExpr)

    val stateInfo =
      if (typedArgs.exists(_.tpe.isErrorType)) Left(Error.DummyError)
      else self.lookupStage(generate.target, typedArgs.map(_.tpe.asRefType))(generate.position, global) match {
        case LookupResult.LookupFailure(err) => Left(err)
        case LookupResult.LookupSuccess(stage) =>
          verifyInitState(stage, generate.state, generate.position)
            .map{ state => (stage, state) }
      }

    stateInfo match {
      case Right((stage, state)) =>
        generate.copy(args = typedArgs, state = state)
          .setSymbol(stage.stage)
          .setTpe(stage.stageTpe.returnType)
      case Left(err) =>
        global.repo.error.append(err)
        generate.copy(args = typedArgs)
          .setSymbol(Symbol.ErrorSymbol)
          .setTpe(Type.ErrorType)
    }
  }

  private def verifyInitState(stage: StageResult, state: Option[StateInfo], pos: Position)(implicit ctx: Context.NodeContext, global: GlobalData): Either[Error, Option[StateInfo]] = {
    def noStatePattern(tpe: Type.MethodType): Either[Error, Option[StateInfo]] = {
      val states = tpe.declares.toMap.values.collect { case state: Symbol.StateSymbol => state }.toVector

      if (states.isEmpty) Right(Option.empty)
      else Left(Error.RequireStateSpecify(stage.stage, pos))
    }

    def withStatePattern(stage: StageResult, state: String, args: Vector[Expression], info: StateInfo): Either[Error, Option[StateInfo]] = {
      val nameStart = info.position.start
      val nameEndColumn = info.position.start.column + state.length
      val namePos = Position(info.position.filename, nameStart, Point(nameStart.line, nameEndColumn))

      stage.stage.tpe.declares.lookup(state) match {
        case None => Left(Error.SymbolNotFound(state, namePos))
        case Some(symbol) if !symbol.isStateSymbol => Left(Error.SymbolNotFound(state, namePos))
        case Some(stateSymbol: Symbol.StateSymbol) => stateSymbol.tpe match {
          case Type.ErrorType => Left(Error.DummyError)
          case tpe: Type.MethodType =>
            verifyStatePattern(
              stateSymbol,
              tpe.replaceWithMap(stage.hpTable, stage.tpTable),
              state,
              args,
              info
            )
        }
      }
    }

    def verifyStatePattern(symbol: Symbol.StateSymbol, tpe: Type.MethodType, state: String, args: Vector[Expression], info: StateInfo): Either[Error, Option[StateInfo]] = {
      val params = tpe.params
      val typedArgs = args.map(typedExpr)

      lazy val sameLength: Either[Error, Unit] =
        if (typedArgs.length == params.length) Right(())
        else Left(Error.ParameterLengthMismatch(params.length, typedArgs.length, info.position))

      lazy val sameTypes: Either[Error, Unit] =
        (params zip typedArgs)
          .collect { case (param: Type.RefType, arg) => param -> arg }
          .filterNot { case (_, arg) => arg.tpe.isErrorType }
          .filter { case (param, arg) => param != arg.tpe.asRefType }
          .map { case (param, arg) => Error.TypeMismatch(param, arg.tpe.asRefType, arg.position) }
          .combine(errs => Error.MultipleErrors(errs: _*))

      for {
        _ <- sameLength
        _ <- sameTypes
      } yield Some(StateInfo(state, typedArgs, info.position).setSymbol(symbol))
    }

    state match {
      case None => noStatePattern(stage.stageTpe)
      case Some(info @ StateInfo(stateName, args)) => withStatePattern(stage, stateName, args, info)
    }
  }


  def typedRelay(relay: Relay)(implicit ctx: Context.NodeContext, global: GlobalData): Relay = {
    def typedStageRelay(args: Vector[Expression]): Either[Error, Relay] = {
      val self = ctx.self.getOrElse(throw new ImplementationErrorException("stage must be in module instance"))
      val argsHaveError = args.exists(_.tpe.isErrorType)

      def lookupStage: Either[Error, StageResult] =
        self.lookupStage(relay.target, args.map(_.tpe.asRefType))(relay.position, global).toEither

      if(argsHaveError) Left(Error.DummyError)
      else for {
        stage <- lookupStage
        state <- verifyInitState(stage, relay.state, relay.position)
      } yield relay.copy(params = args, state = state).setSymbol(stage.stage).setTpe(Type.unitTpe(global))
    }

    def typedProcRelay(args: Vector[Expression]): Either[Error, Relay] = {
      def findProcSym: Option[Symbol.ProcSymbol] = {
        @tailrec def loop(ctx: Context): Option[Symbol.ProcSymbol] = {
          ctx match {
            case _: Context.RootContext => None
            case c: Context.NodeContext => c.owner match {
              case p: Symbol.ProcSymbol => Some(p)
              case _ => loop(c.parent)
            }
          }
        }

        loop(ctx)
      }

      def verifyNoState: Either[Error, Unit] =
        if(relay.state.isDefined) Left(Error.RelayWithStateInProc(relay.position))
        else Right(())

      def lookupBlock(target: String, proc: Symbol.ProcSymbol): Either[Error, Symbol.ProcBlockSymbol] =
        proc.tpe.declares.lookup(target) match {
          case Some(blk: Symbol.ProcBlockSymbol) => Right(blk)
          case Some(sym) => Left(Error.RequireSymbol[Symbol.ProcBlockSymbol](sym, relay.position))
          case None => Left(Error.SymbolNotFound(target, relay.position))
        }

      def verifyArguments(blk: Symbol.ProcBlockSymbol, args: Vector[Expression]): Either[Error, Unit] = {
        if(args.exists(_.tpe.isErrorType))
          return Left(Error.DummyError)

        val paramTpes = blk.tpe.asMethodType.params

        if(paramTpes.length != args.length)
          return Left(Error.ParameterLengthMismatch(paramTpes.length, args.length, relay.position))

        val errs = (paramTpes zip args)
          .filter{ case (p, a) => p != a.tpe }
          .map{ case (p, a) => Error.TypeMismatch(p, a.tpe.asRefType, a.position) }

        if(errs.isEmpty) Right(())
        else Left(Error.MultipleErrors(errs: _*))
      }

      val procSymbol = findProcSym.getOrElse(throw new ImplementationErrorException("proc's blocks must be under proc definition"))
      for {
        _ <- verifyNoState
        pblk <- lookupBlock(relay.target, procSymbol)
        _ <- verifyArguments(pblk, args)
      } yield relay.copy(params = args).setSymbol(pblk).setTpe(Type.unitTpe)
    }

    val typedArgs = relay.params.map(typedExpr)
    val result = ctx.owner match {
      case s: Symbol.StageSymbol     => typedStageRelay(typedArgs)
      case _: Symbol.StateSymbol     => typedStageRelay(typedArgs)
      case _: Symbol.ProcBlockSymbol => typedProcRelay(typedArgs)
      case _ => Left(Error.RelayOutsideStageOrProc(relay.position))
    }

    result match {
      case Right(relay) => relay
      case Left(err) =>
        global.repo.error.append(err)
        relay.setSymbol(Symbol.ErrorSymbol).setTpe(Type.ErrorType)
    }

    /*
    def verifyRelayTarget: Relay = {
      val self = ctx.self.getOrElse(throw new ImplementationErrorException("stage must be in module instance"))
      val typedArgs = relay.params.map(typedExpr)

      val (symbol, tpe) =
        if (typedArgs.exists(_.tpe.isErrorType)) (Symbol.ErrorSymbol, Type.ErrorType)
        else {
          self.lookupStage(relay.target, typedArgs.map(_.tpe.asRefType))(relay.position, global) match {
            case LookupResult.LookupSuccess((symbol, tpe)) => (symbol, tpe.returnType)
            case LookupResult.LookupFailure(err) =>
              global.repo.error.append(err)
              (Symbol.ErrorSymbol, Type.ErrorType)
          }
        }

      val result = symbol match {
        case Symbol.ErrorSymbol => Left(Error.DummyError)
        case stage: Symbol.StageSymbol => verifyInitState(stage, relay.state, relay.position)
      }

      val (relaySymbol, relayTpe, stateInfo) = result match {
        case Right(state) => (symbol, tpe, state)
        case Left(err) =>
          global.repo.error.append(err)
          (Symbol.ErrorSymbol, Type.ErrorType, relay.state)
      }

      Relay(relay.target, typedArgs, stateInfo, relay.position)
        .setSymbol(relaySymbol)
        .setTpe(relayTpe)
        .setID(relay.id)
    }

    val result = ctx.owner match {
      case _: Symbol.StageSymbol => verifyRelayTarget
      case _: Symbol.StateSymbol => verifyRelayTarget
      case _ =>
        global.repo.error.append(Error.RelayOutsideStageOrProc(relay.position))
        relay.setSymbol(Symbol.ErrorSymbol).setTpe(Type.ErrorType)
    }
     */
  }

  def typedReturn(ret: Return)(implicit ctx: Context.NodeContext, global: GlobalData): Return = {
    def inFinalBlock(blk: Symbol.ProcBlockSymbol): Either[Error, Unit] = {
      if(blk.flag.hasFlag(Modifier.Final)) Right(())
      else Left(Error.ReturnFromNonFinal(blk, ret.position))
    }

    def typecheck(proc: Symbol.ProcSymbol, expr: Expression): Either[Error, Unit] = {
      val retTpe = proc.tpe.asMethodType.returnType
      val expectTpe = Type.RefType(retTpe.origin, retTpe.hardwareParam, retTpe.typeParam, isPointer = false)

      expr.tpe match {
        case Type.ErrorType => Left(Error.DummyError)
        case tpe: Type.RefType =>
          if (tpe == expectTpe) Right(())
          else Left(Error.TypeMismatch(expectTpe, tpe, expr.position))
      }
    }

    val typedRetExpr = typedExpr(ret.expr)

    val result = ctx.owner match {
      case blk: Symbol.ProcBlockSymbol =>
        val proc = ctx.owners(1).asProcSymbol

        for {
          _ <- inFinalBlock(blk)
          _ <- typecheck(proc, typedRetExpr)
        } yield ()
      case _ => Left(Error.ReturnOutsideProcBlock(ret.position))
    }

    result.left.foreach(global.repo.error.append)
    ret.copy(expr = typedRetExpr).setTpe(Type.unitTpe)
  }

  def typedHPExpr(expr: HPExpr)(implicit ctx: Context.NodeContext, global: GlobalData): HPExpr = expr match {
    case ident: Ident => typedHPIdent(ident)
    case binop: HPBinOp => typedHPBinOp(binop)
    case literal: IntLiteral => typedHPIntLit(literal)
    case literal: StringLiteral => typedHPStrLit(literal)
    case unary @ HPUnaryOp(ident) =>
      val typedIdent = typedHPIdent(ident)
      HPUnaryOp(typedIdent, expr.position)
        .setSymbol(typedIdent.symbol)
        .setTpe(typedIdent.tpe)
        .setID(unary.id)
  }

  def typedHPIdent(ident: Ident)(implicit ctx: Context.NodeContext, global: GlobalData): Ident = {
    def verifyType(symbol: Symbol): Either[Error, Unit] = symbol.tpe match {
      case Type.ErrorType => Left(Error.DummyError)
      case tpe: Type.RefType if tpe =:= Type.numTpe => Right(())
      case tpe: Type.RefType if tpe =:= Type.strTpe => Right(())
      case tpe: Type.RefType => Left(Error.RequireSpecificType(tpe, Seq(Type.numTpe, Type.strTpe), ident.position))
    }

    val symbol = for {
      symbol <- ctx.lookup[Symbol.TermSymbol](ident.name).toEither
      _ <- verifyType(symbol)
    } yield symbol

    symbol match {
      case Left(err) =>
        global.repo.error.append(err)
        ident.setTpe(Type.ErrorType).setSymbol(Symbol.ErrorSymbol)
      case Right(symbol) =>
        ident.setTpe(symbol.tpe).setSymbol(symbol)
    }
  }

  def typedHPBinOp(binop: HPBinOp)(implicit ctx: Context.NodeContext, global: GlobalData): HPBinOp = {
    val typedLeft = typedHPExpr(binop.left)
    val typedRight = typedHPExpr(binop.right)

    val opStart = binop.left.position.end
    val opEnd = binop.right.position.start
    val opPos = Position(binop.left.position.filename, opStart, opEnd)

    val isValid = (typedLeft.tpe =:= Type.numTpe) && (typedRight.tpe =:= Type.numTpe)
    val hasStrTpe = (typedLeft.tpe =:= Type.strTpe) || (typedRight.tpe =:= Type.strTpe)
    val tpe =
      if (isValid) Type.numTpe
      else if (hasStrTpe) {
        global.repo.error.append(Error.SymbolNotFound("+", opPos))
        Type.ErrorType
      }
      else Type.ErrorType

    HPBinOp(typedLeft, typedRight, binop.position).setTpe(tpe).setID(binop.id)
  }

  def typedHPIntLit(int: IntLiteral)(implicit global: GlobalData): IntLiteral = {
    int.setTpe(Type.numTpe)
  }

  def typedHPStrLit(str: StringLiteral)(implicit global: GlobalData): StringLiteral = {
    str.setTpe(Type.strTpe)
  }

  /*
  def verifyParamTypes(expect: Vector[Type], actual: Vector[Type])(implicit ctx: Context.NodeContext, global: GlobalData): Vector[Error] = {
    if (expect.length != actual.length)
      return Vector(Error.ParameterLengthMismatch(expect.length, actual.length))

    (expect zip actual)
      .collect {
        case (e: Type.RefType, a: Type.RefType) => (e, a)
      }
      .filter {
        case (e, a) => a =:= e
      }
      .map {
        case (e, a) => Error.TypeMismatch(e, a, )
      }
  }
  */

  def typedFieldTypeParam(tpeDef: TypeDef)(implicit ctx: Context.NodeContext, global: GlobalData): TypeDef = {
    tpeDef.symbol.tpe

    val tpeTree = global.cache.get(tpeDef.tpe.get).get.asInstanceOf[TypeTree]
    val typedTpeDef = tpeDef.copy(name = tpeDef.name, tpe = Some(tpeTree))
      .setSymbol(tpeDef.symbol)
      .setID(tpeDef.id)

    global.cache.set(typedTpeDef)
    typedTpeDef
  }
}