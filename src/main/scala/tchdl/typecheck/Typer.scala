package tchdl.typecheck

import tchdl.ast._
import tchdl.util.TchdlException.ImplementationErrorException
import tchdl.util._

object Typer {
  def exec(cu: CompilationUnit)(implicit global: GlobalData): CompilationUnit = {
    implicit val ctx: Context.RootContext = getContext(cu.pkgName, cu.filename.get)

    val topDefs = cu.topDefs.map(diveIntoExpr)

    CompilationUnit(cu.filename, cu.pkgName, cu.imports, topDefs)
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
          case stageDef:  StageDef => typedStageDef(stageDef)(implBodyCtx, global)
          case alwaysDef: AlwaysDef => typedAlwaysDef(alwaysDef)(implBodyCtx, global)
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

    if(!typedBody.tpe.isErrorType && typedBody.tpe.asRefType != methodTpe.returnType) {
      global.repo.error.append(Error.TypeMismatch(methodTpe.returnType, typedBody.tpe.asRefType))
    }

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

    if(!vdefTpe.isErrorType) {
      def typecheck(tree: Option[AST with HasType]): Unit = {
        tree.filterNot(_.tpe.isErrorType)
          .filterNot(_.tpe =:= vdefTpe)
          .foreach(t => global.repo.error.append(Error.TypeMismatch(vdefTpe, t.tpe)))
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
      .filterNot(_ =:= typedConstruct.tpe.asRefType)
      .map(tpe => Error.TypeMismatch(tpe, typedConstruct.tpe.asRefType))
      .foreach(global.repo.error.append)

    val typedValDef = ValDef(valDef.flag, name, typedTpeTree, Some(typedConstruct))
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
          case exprTpe: Type.RefType if exprTpe =!= vdefTpe => Left(Error.TypeMismatch(vdefTpe, exprTpe))
          case _: Type.RefType => Right(typedExpr)
        }
    }

    result match {
      case Right(expr) =>
        val typeTree =  vdef.tpeTree.map(_.setTpe(vdef.symbol.tpe))
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
      case vdef: ValDef => typedExprValDef(vdef)(stageBodyCtx, global)
      case expr: Expression => typedExpr(expr)(stageBodyCtx, global)
    }
    val typedStates = stageDef.states.map(typedStateDef(_)(stageBodyCtx, global))

    stageDef.copy(states = typedStates, blk = typedBodyElems).setSymbol(stageDef.symbol.asStageSymbol).setID(stageDef.id)
  }

  def typedStateDef(stateDef: StateDef)(implicit ctx: Context.NodeContext, global: GlobalData): StateDef = {
    val stateSigCtx = Context(ctx, stateDef.symbol)
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
      case ifExpr: IfExpr => typedIfExpr(ifExpr)
      case self: This => typedThis(self)
      case blk: Block => typedBlock(blk)
      case construct: ConstructClass => typedConstructClass(construct)
      case construct: ConstructModule => typedConstructModule(construct)
      case construct: ConstructEnum => typedConstructEnum(construct)
      case int: IntLiteral => typedIntLiteral(int)
      case bool: BoolLiteral => typedBoolLiteral(bool)
      case unit: UnitLiteral => typedUnitLiteral(unit)
      case bit: BitLiteral => typedBitLiteral(bit)
      case apply: Apply => typedExprApply(apply)
      case generate: Generate => typedGenerate(generate)
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
        ident.setTpe(symbol.tpe.asRefType).setSymbol(symbol)
    }
  }

  def typedExprApply(apply: Apply)(implicit ctx: Context.NodeContext, global: GlobalData): Apply = {
    val typedArgs = apply.args.map(typedExpr)
    val typedHPs = apply.hps.map(typedHPExpr)
    val typedTPs = apply.tps.map(typedTypeTree)

    val hasError =
      typedArgs.exists(_.tpe.isErrorType) &&
        typedHPs.exists(_.tpe.isErrorType) &&
        typedTPs.exists(_.tpe.isErrorType)

    lazy val errorApply =
      Apply(apply.prefix, typedHPs, typedTPs, typedArgs)
        .setTpe(Type.ErrorType)
        .setID(apply.id)

    def lookupMethodForIdent(ident: Ident): Either[Error, Apply] = {
      def verifyMethodValidity(method: Symbol.MethodSymbol): Either[Error, Unit] = {
        method.tpe match {
          case Type.ErrorType => Left(Error.DummyError)
          case tpe: Type.MethodType =>
            if((tpe.params :+ tpe.returnType ).exists(_.isErrorType)) Left(Error.DummyError)
            else if (method.hps.exists(_.tpe.isErrorType)) Left(Error.DummyError)
            else Right(())
        }
      }

      def verifyLength(methodSymbol: Symbol.MethodSymbol, methodType: Type.MethodType): Either[Error, Unit] = {
        def verify(builder: (Int, Int) => Error)(expect: Int, actual: Int, errs: Vector[Error]): Vector[Error] =
          if(expect == actual) errs
          else errs :+ builder(expect, actual)

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

        if(errs.isEmpty) Right(())
        else Left(Error.MultipleErrors(errs: _*))
      }

      def verifyHPType(methodSymbol: Symbol.MethodSymbol): Either[Error, Unit] = {
        val results = (methodSymbol.hps.map(_.tpe) zip typedHPs.map(_.tpe)).map {
          case (p: Type.RefType, a: Type.RefType) =>
            if(p =:= a) Right(())
            else Left(Error.TypeMismatch(p, a))
        }

        val (errs, _) = results.partitionMap(identity)
        if(errs.isEmpty) Right(())
        else Left(Error.MultipleErrors(errs: _*))
      }

      def verifyEachBounds(hpBounds: Vector[HPBound], tpBounds: Vector[TPBound]): Either[Error, Unit] = {
        val (hpErrs, _) = hpBounds.map(HPBound.verifyMeetBound(_, ctx.hpBounds)).partitionMap(identity)
        val (tpErrs, _) = tpBounds.map(TPBound.verifyMeetBound(_, ctx.hpBounds, ctx.tpBounds)).partitionMap(identity)
        val errs = hpErrs ++ tpErrs

        if(errs.isEmpty) Right(())
        else Left(Error.MultipleErrors(errs: _*))
      }

      ctx.root.lookup[Symbol.MethodSymbol](ident.name) match {
        case LookupResult.LookupFailure(err) => Left(err)
        case LookupResult.LookupSuccess(methodSymbol) => for {
          _ <- verifyMethodValidity(methodSymbol)
          methodType = methodSymbol.tpe.asMethodType
          _ <- verifyLength(methodSymbol, methodType)
          _ <- verifyHPType(methodSymbol)
          hpTable = (methodSymbol.hps zip typedHPs).toMap
          tpTable = (methodSymbol.tps zip typedTPs.map(_.tpe.asRefType)).toMap
          swappedHPBound = HPBound.swapBounds(methodSymbol.hpBound, hpTable)
          swappedTPBound = TPBound.swapBounds(methodSymbol.tpBound, hpTable, tpTable)
          _ <- verifyEachBounds(swappedHPBound, swappedTPBound)
          replacedTpe = methodType.replaceWithMap(hpTable, tpTable)
          _ <- Type.RefType.verifyMethodType(replacedTpe, typedArgs.map(_.tpe.asRefType))
          typedApply = Apply(
            ident.setTpe(replacedTpe).setSymbol(methodSymbol),
            typedHPs,
            typedTPs,
            typedArgs
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
      )

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
            Select(typedPrefix, select.name)
              .setSymbol(symbol)
              .setTpe(tpe)
              .setID(select.id)

          Apply(typedSelect, typedHPs, typedTPs, typedArgs)
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
          StaticSelect(prefixTree, select.name)
            .setTpe(tpe)
            .setSymbol(symbol)
            .setID(select.id)

        Apply(typedSelect, typedHPs, typedTPs, typedArgs)
          .setTpe(tpe.returnType)
          .setID(apply.id)
      }
    }

    if(hasError) errorApply
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
    val typedSuffix = typedExpr(select.prefix)
    typedSuffix.tpe match {
      case refTpe: Type.RefType =>
        // This method only for reference to field of struct or module.
        // That's why this method does not look up method.
        refTpe.lookupField(select.name, ctx.hpBounds, ctx.tpBounds) match {
          case LookupResult.LookupFailure(err) =>
            global.repo.error.append(err)
            select.copy(typedSuffix, select.name)
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
                    .map { case (sym, expr) => sym -> expr}
                    .toMap
              }

            val selectTpe = symbol.tpe match {
              case tpe: Type.RefType => tpe.replaceWithMap(hpTable, tpTable)
              case tpe: Type.MethodType => tpe.replaceWithMap(hpTable, tpTable)
              case Type.ErrorType => Type.ErrorType
            }

            select.copy(typedSuffix, select.name)
              .setTpe(selectTpe)
              .setSymbol(symbol)
              .setID(select.id)
        }
      case Type.ErrorType =>
        select.copy(typedSuffix, select.name)
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

    val err = targetTpe.lookupField(pair.name, ctx.hpBounds, ctx.tpBounds) match {
      case LookupResult.LookupFailure(err) => Some(err)
      case LookupResult.LookupSuccess(symbol) => (symbol.tpe, typedInit.tpe) match {
        case (Type.ErrorType, _) => Some(Error.DummyError)
        case (_, Type.ErrorType) => Some(Error.DummyError)
        case (fieldTpe: Type.RefType, exprTpe: Type.RefType) =>
          val replacedFieldTpe = fieldTpe.replaceWithMap(hpTable, tpTable)
          if(replacedFieldTpe =:= exprTpe) None
          else Some(Error.TypeMismatch(fieldTpe, exprTpe))
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
        val err = Error.InvalidFormatForModuleConstruct(expr)
        val typedExpr = expr match {
          case e: Expression with HasSymbol => e.setTpe(Type.ErrorType).setSymbol(Symbol.ErrorSymbol)
          case e => e.setTpe(Type.ErrorType)
        }

        (Some(err), typedExpr)
    }

    val typedPair = ConstructPair(pair.name, typedInit).setID(pair.id)

    val pairErr = targetTpe.lookupField(pair.name, ctx.hpBounds, ctx.tpBounds) match {
      case LookupResult.LookupFailure(err) => Some(err)
      case LookupResult.LookupSuccess(symbol) => (symbol.tpe, typedInit.tpe) match {
        case (Type.ErrorType, _) => Some(Error.DummyError)
        case (_, Type.ErrorType) => Some(Error.DummyError)
        case (fieldTpe: Type.RefType, exprTpe: Type.RefType) =>
          val replacedFieldTpe = fieldTpe.replaceWithMap(hpTable, tpTable)
          if(replacedFieldTpe =:= exprTpe) None
          else Some(Error.TypeMismatch(fieldTpe, exprTpe))
      }
    }

    val errs = Vector(err, pairErr).flatten
    val combinedErr =
      if(errs.isEmpty) None
      else Some(Error.MultipleErrors(errs: _*))

    (combinedErr, typedPair)
  }

  def typedMatch(matchExpr: Match)(implicit ctx: Context.NodeContext, global: GlobalData): Match = {
    def typedCase(caseDef: Case, isHardwareMatch: Boolean): Case = {
      val caseCtx = Context(ctx)

      typedEnumPattern(caseDef.pattern, caseCtx, isHardwareMatch) match {
        case Left(enum) => Case(enum, caseDef.exprs).setTpe(Type.ErrorType).setID(caseDef.id)
        case Right(enum) =>
          val blockElems = caseDef.exprs.map {
            case expr: Expression => typedExpr(expr)(caseCtx, global)
            case vdef: ValDef => typedValDef(vdef)(caseCtx, global)
          }

          val retTpe = blockElems.last.asInstanceOf[Expression].tpe
          Case(enum, blockElems).setTpe(retTpe).setID(caseDef.id)
      }
    }

    def verifyEnumPattern(symbol: Symbol.EnumMemberSymbol, target: Type.RefType, exprs: Vector[PatternExpr], ctx: Context.NodeContext): Either[Error, Unit] = {
      def typeCheck(expect: Type.RefType, actual: Type.RefType): Either[Error, Unit] =
        if (actual == expect) Right(())
        else Left(Error.TypeMismatch(expect, actual))

      val hpTable = (target.origin.hps zip target.hardwareParam).toMap
      val tpTable = (target.origin.tps zip target.typeParam).toMap

      val fieldTpes = symbol.tpe.asEnumMemberType.fields
        .map(_.tpe.asRefType)
        .map(_.replaceWithMap(hpTable, tpTable))

      if(fieldTpes.length != exprs.length) Left(Error.ParameterLengthMismatch(fieldTpes.length, exprs.length))
      else {
        val results = (exprs zip fieldTpes).map {
          case (_: IntLiteral, tpe) => typeCheck(Type.intTpe, tpe)
          case (_: UnitLiteral, tpe) => typeCheck(Type.unitTpe, tpe)
          case (BitLiteral(_, width), tpe) => typeCheck(Type.bitTpe(IntLiteral(width)), tpe)
          case (ident @ Ident(name), tpe) =>
            val symbol = Symbol.VariableSymbol.local(
              name,
              ctx.path,
              Accessibility.Private,
              Modifier.Local,
              tpe
            )

            ident.setSymbol(symbol).setTpe(tpe)
            ctx.append(symbol)
        }

        results.combine(errs => Error.MultipleErrors(errs: _*))
      }
    }

    def typedEnumPattern(enum: EnumPattern, ctx: Context.NodeContext, isHardwareMatch: Boolean): Either[EnumPattern, EnumPattern] = {
      val EnumPattern(target, exprs) = enum
      val typedTarget = typedTypeTree(target)(ctx, global)

      def typedEnum: EnumPattern = EnumPattern(typedTarget, exprs).setID(enum.id)

      val usageErrors = exprs
        .collect{ case _: BitLiteral if !isHardwareMatch => Some(Error.CannotUseBitLitForSWPattern(typedTarget.tpe))}
        .flatten

      val result = typedTarget.symbol match {
        case Symbol.ErrorSymbol => Left(Error.DummyError)
        case symbol: Symbol.EnumMemberSymbol => verifyEnumPattern(symbol, typedTarget.tpe.asRefType, exprs, ctx)
        case symbol => Left(Error.RequireSymbol[Symbol.EnumMemberSymbol](symbol))
      }

      result.left.foreach(global.repo.error.append)
      usageErrors.foreach(global.repo.error.append)
      result match {
        case Right(_) if usageErrors.isEmpty => Right(typedEnum)
        case _ => Left(typedEnum)
      }
    }

    val Match(matched, cases) = matchExpr
    val typedMatched = typedExpr(matched)

    typedMatched.tpe match {
      case Type.ErrorType => Match(typedMatched, cases).setTpe(Type.ErrorType).setID(matchExpr.id)
      case tpe: Type.RefType =>
        val isHardwareMatch = tpe.isHardwareType
        val typedCases = cases.map(typedCase(_, isHardwareMatch))

        def hasError: Either[Error, Unit] =
          if(typedCases.map(_.tpe).exists(_.isErrorType)) Left(Error.DummyError)
          else Right(())

        def typeMismatches: Either[Error, Unit] = {
          val retTpes = typedCases.map(_.tpe.asRefType)
          val errs = retTpes.filter(_ != retTpes.last).map(Error.TypeMismatch(retTpes.last, _))

          if(errs.isEmpty) Right(())
          else Left(Error.MultipleErrors(errs: _*))
        }

        def patternTypeMismatch: Either[Error, Unit] = {
          val patternTypes = typedCases
            .map{ case Case(pattern, _) => pattern }
            .map{ _.target.tpe.asRefType }

          val errs = patternTypes.filter(_ != tpe).map(Error.TypeMismatch(tpe, _))

          if(errs.isEmpty) Right(())
          else Left(Error.MultipleErrors(errs: _*))
        }

        def hasFullPatterns: Either[Error, Unit] = {
          tpe.origin match {
            case symbol: Symbol.EnumSymbol =>
              val allMembers = symbol.tpe.declares.toMap.values.toVector.map(_.asEnumMemberSymbol).toSet
              val exhaustiveCaseMembers = typedCases
                .map(_.pattern)
                .filter(_.exprs.forall(_.isInstanceOf[Ident]))
                .map(_.target.symbol.asEnumMemberSymbol)

              val remains = exhaustiveCaseMembers.foldLeft(allMembers) {
                case (remains, member) => remains - member
              }

              if(remains.isEmpty) Right(())
              else Left(Error.NotExhaustiveEnum(remains.toVector))
          }
        }

        def retIsNotHeapType(retTpe: Type.RefType): Either[Error, Unit] = {
          if(retTpe.isHardwareType) Right(())
          else Left(Error.RejectHeapType(retTpe))
        }

        val result = for {
          _ <- hasError
          _ <- typeMismatches
          _ <- patternTypeMismatch
          _ <- hasFullPatterns
          _ <- retIsNotHeapType(typedCases.head.tpe.asRefType)
        } yield Match(typedMatched, typedCases)
          .setTpe(typedCases.head.tpe)
          .setID(matchExpr.id)

        result match {
          case Right(matchExpr) => matchExpr
          case Left(err) =>
            global.repo.error.append(err)
            Match(typedMatched, typedCases)
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
            ConstructClass(typedTarget, typedPairs)
              .setSymbol(typedTarget.symbol)
              .setTpe(tpe)
              .setID(construct.id)
          case _: Symbol.ModuleSymbol if construct.fields.isEmpty =>
            ConstructModule(typedTarget, Vector.empty, Vector.empty)
              .setSymbol(typedTarget.symbol)
              .setTpe(tpe)
              .setID(construct.id)
          case _: Symbol.ModuleSymbol =>
            global.repo.error.append(Error.RequireParentOrSiblingIndicator(construct))
            ConstructClass(typedTarget, typedPairs)
              .setSymbol(Symbol.ErrorSymbol)
              .setTpe(Type.ErrorType)
              .setID(construct.id)
          case _: Symbol.InterfaceSymbol =>
            global.repo.error.append(Error.TryToConstructInterface(construct))
            ConstructClass(typedTarget, typedPairs)
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
            global.repo.error.append(Error.RejectParentOrSiblingIndicator(construct))
            Type.ErrorType
          case _: Symbol.InterfaceSymbol =>
            global.repo.error.append(Error.TryToConstructInterface(construct))
            Type.ErrorType
        }

        ConstructModule(typedTarget, typedParents, typedSiblings)
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
        if(declares.length == fields.length) Right(())
        else Left(Error.ParameterLengthMismatch(declares.length, fields.length))

      def verifyFieldExprType =
        if(fields.exists(_.tpe.isErrorType)) Left(Error.DummyError)
        else Right(())

      def typeMismatches(
        hpTable: Map[Symbol.HardwareParamSymbol, HPExpr],
        tpTable: Map[Symbol.TypeParamSymbol, Type.RefType]
      ): Vector[Error.TypeMismatch] = {
        val expectTpes = declares
          .map{ case (_, symbol) => symbol }
          .map(_.tpe.asRefType)
          .map(_.replaceWithMap(hpTable, tpTable))

        expectTpes
          .zip(fields.map(_.tpe.asRefType))
          .filter{ case (field, expr) => field != expr }
          .map{ case (field, expr) => Error.TypeMismatch(field, expr) }
      }

      def verifyTypeMatching: Either[Error, Unit] = {
        val hpTable = (parent.origin.hps zip parent.hardwareParam).toMap
        val tpTable = (parent.origin.tps zip parent.typeParam).toMap

        val mismatches = typeMismatches(hpTable, tpTable)

        if(mismatches.isEmpty) Right(())
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
        case tpe: Type.RefType => Left(Error.ConstructEnumForm(tpe))
        case Type.ErrorType => Left(Error.DummyError)
      }
    }

    val tpe = result match {
      case Right(tpe) => tpe
      case Left(err) =>
        global.repo.error.append(err)
        Type.ErrorType
    }

    ConstructEnum(typedTarget, typedFields)
      .setSymbol(typedTarget.symbol)
      .setTpe(tpe)
      .setID(construct.id)
  }

  def typedStdBinOp(binop: StdBinOp)(implicit ctx: Context.NodeContext, global: GlobalData): StdBinOp = {
    val typedLeft = typedExpr(binop.left)
    val typedRight = typedExpr(binop.right)

    val result = (typedLeft.tpe, typedRight.tpe) match {
      case (Type.ErrorType, _) => LookupResult.LookupFailure(Error.DummyError)
      case (_, Type.ErrorType) => LookupResult.LookupFailure(Error.DummyError)
      case (leftTpe: Type.RefType, rightTpe: Type.RefType) =>
        leftTpe.lookupOperator(binop.op, Some(rightTpe), ctx.hpBounds, ctx.tpBounds)
    }

    result match {
      case LookupResult.LookupFailure(err) =>
        global.repo.error.append(err)
        binop.setSymbol(Symbol.ErrorSymbol).setTpe(Type.ErrorType)
      case LookupResult.LookupSuccess((methodSymbol, methodTpe)) =>
        StdBinOp(binop.op, typedLeft, typedRight)
          .setSymbol(methodSymbol)
          .setTpe(methodTpe.returnType)
          .setID(binop.id)
    }
  }

  def typedStdUnaryOp(unaryOp: StdUnaryOp)(implicit ctx: Context.NodeContext, global: GlobalData): StdUnaryOp = {
    val typedOperand = typedExpr(unaryOp.operand)

    val result = typedOperand.tpe match {
      case Type.ErrorType => LookupResult.LookupFailure(Error.DummyError)
      case operand: Type.RefType => operand.lookupOperator(unaryOp.op, None, ctx.hpBounds, ctx.tpBounds)
    }

    result match {
      case LookupResult.LookupFailure(err) =>
        global.repo.error.append(err)
        unaryOp.setSymbol(Symbol.ErrorSymbol).setTpe(Type.ErrorType)
      case LookupResult.LookupSuccess((symbol, tpe)) =>
        unaryOp.setSymbol(symbol).setTpe(tpe.returnType)
    }
  }


  def typedBlock(blk: Block)(implicit ctx: Context.NodeContext, global: GlobalData): Block = {
    val blkCtx = Context.blk(ctx)

    val typedElems = blk.elems.map {
      case vdef: ValDef => typedExprValDef(vdef)(blkCtx, global)
      case expr: Expression => typedExpr(expr)(blkCtx, global)
    }

    val typedLast = typedExpr(blk.last)(blkCtx, global)

    Block(typedElems, typedLast).setTpe(typedLast.tpe).setID(blk.id)
  }

  def typedThis(self: This)(implicit ctx: Context.NodeContext, global: GlobalData): This = {
    val tpe = ctx.self match {
      case None =>
        global.repo.error.append(Error.UsingSelfOutsideClass)
        Type.ErrorType
      case Some(_) if ctx.isStatic =>
        global.repo.error.append(Error.UsingSelfInsideStatic)
        Type.ErrorType
      case Some(tpe) =>
        tpe
    }

    This().setTpe(tpe).setID(self.id)
  }

  def typedIfExpr(ifexpr: IfExpr)(implicit ctx: Context.NodeContext, global: GlobalData): IfExpr = {
    val typedCond = typedExpr(ifexpr.cond)
    val typedConseq = typedExpr(ifexpr.conseq)
    val typedAlt = ifexpr.alt.map(typedExpr)

    def isBoolTpe = typedCond.tpe =:= Type.boolTpe
    def isBit1Tpe = typedCond.tpe =:= Type.bitTpe(IntLiteral(1))
    def isErrorTpe = typedCond.tpe.isErrorType
    if (!isErrorTpe && !isBoolTpe && !isBit1Tpe)
      global.repo.error.append(Error.RequireSpecificType(typedCond.tpe.asRefType, Type.boolTpe, Type.bitTpe(IntLiteral(1))))

    typedAlt match {
      case None =>
        IfExpr(typedCond, typedConseq, typedAlt).setTpe(Type.unitTpe).setID(ifexpr.id)
      case Some(alt) =>
        val retTpe = (alt.tpe, typedConseq.tpe) match {
          case (Type.ErrorType, tpe) => tpe
          case (tpe, Type.ErrorType) => tpe
          case (altTpe: Type.RefType, conseqTpe: Type.RefType)  =>
            if(altTpe != conseqTpe)
              global.repo.error.append(Error.TypeMismatch(altTpe, conseqTpe))

            if(!altTpe.isHardwareType)
              global.repo.error.append(Error.RejectHeapType(altTpe))

            altTpe
        }



        IfExpr(typedCond, typedConseq, typedAlt).setTpe(retTpe).setID(ifexpr.id)
    }
  }

  def typedTypeTree(typeTree: TypeTree)(implicit ctx: Context.NodeContext, global: GlobalData): TypeTree = {
    def verifyHP(symbol: Symbol.TypeSymbol, typedHPs: Vector[HPExpr]): Either[Error, Unit] = {
      val invalidHPLength = symbol.hps.length != typedHPs.length
      val hasError = typedHPs.exists(_.tpe.isErrorType)

      if(invalidHPLength) Left(Error.HardParameterLengthMismatch(symbol.hps.length, typeTree.hp.length))
      else if(hasError) Left(Error.DummyError)
      else {
        val table = (symbol.hps zip typedHPs).toMap
        val swapped = HPBound.swapBounds(symbol.hpBound, table)

        val (errs, _) = swapped
          .map(HPBound.verifyMeetBound(_, ctx.hpBounds))
          .partitionMap(identity)

        if(errs.isEmpty) Right(())
        else Left(Error.MultipleErrors(errs: _*))
      }
    }

    def verifyTP(symbol: Symbol.TypeSymbol, typedHPs: Vector[HPExpr], typedTPs: Vector[TypeTree]): Either[Error, Unit] = {
      val invalidTPLength = symbol.tps.length != typedTPs.length
      lazy val hasError = typedTPs.exists(_.tpe.isErrorType)
      lazy val tpRefTpe = typedTPs.map(_.tpe.asRefType)

      if(invalidTPLength) Left(Error.TypeParameterLengthMismatch(symbol.tps.length, typedTPs.length))
      else if(hasError) Left(Error.DummyError)
      else {
        val hpTable = (symbol.hps zip typedHPs).toMap
        val tpTable = (symbol.tps zip tpRefTpe).toMap
        val swapped = TPBound.swapBounds(symbol.tpBound, hpTable, tpTable)
        val (errs, _) = swapped
          .map(TPBound.verifyMeetBound(_, ctx.hpBounds, ctx.tpBounds))
          .partitionMap(identity)

        if(errs.isEmpty) Right(())
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
            val tpe = Type.RefType(symbol, hargs, targs.map(_.tpe.asRefType))

            TypeTree(ident.setTpe(symbol.tpe).setSymbol(symbol), hargs, targs)
              .setTpe(tpe)
              .setSymbol(symbol)
              .setID(typeTree.id)
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
        symbol <- prefix.tpe.asRefType.lookupType[Symbol.TypeSymbol](select.name).toEither
        _ <- verifyHP(symbol, hargs)
        _ <- verifyTP(symbol, hargs, targs)
      } yield (prefix, symbol)

      result match {
        case Left(err) => Left(err)
        case Right(pair) =>
          val (symbol, tpe) = pair match {
            case (prefix, symbol: Symbol.EnumMemberSymbol) => (symbol, prefix.tpe)
            case (_, symbol) => (symbol, symbol.tpe)
          }

          val (prefix, _) = pair

          val typedSelect = StaticSelect(prefix, select.name)
            .setSymbol(symbol)
            .setTpe(tpe)
            .setID(select.id)

          Right(TypeTree(typedSelect, hargs, targs).setTpe(tpe).setSymbol(symbol).setID(typeTree.id))
      }
    }

    def typedForSelectPackage(select: SelectPackage, hargs: Vector[HPExpr], targs: Vector[TypeTree]): Either[Error, TypeTree] = {
      def lookupPackageFromCtx: Either[Error, Symbol.PackageSymbol] = {
        val head = ctx.lookup[Symbol.PackageSymbol](select.packages.head).toEither

        select.packages.tail.foldLeft(head){
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
        val tpe = Type.RefType(typeSymbol, hargs, targs.map(_.tpe.asRefType))

        TypeTree(typedSelect, hargs, targs)
          .setSymbol(typeSymbol)
          .setTpe(tpe)
          .setID(typeTree.id)
      }
    }

    def typedForThisType(thisTree: ThisType): Either[Error, TypeTree] =
      ctx.self match {
        case None => Left(Error.SelfTypeNotFound)
        case Some(tpe) =>
          val tree = ThisType().setSymbol(tpe.origin).setTpe(tpe).setID(thisTree.id)
          val tpeTree = TypeTree(tree, Vector.empty, Vector.empty)
            .setSymbol(tree.symbol)
            .setTpe(tree.tpe)

          Right(tpeTree)
      }



    def execTyped(hargs: Vector[HPExpr], targs: Vector[TypeTree]): Either[Error, TypeTree] =
      typeTree.expr match {
        case ident: Ident => typedForIdent(ident, hargs, targs)
        case select: StaticSelect => typedForStaticSelect(select, hargs, targs)
        case select: SelectPackage => typedForSelectPackage(select, hargs, targs)
        case tree: ThisType => typedForThisType(tree)
      }

    val typedHArgs = typeTree.hp.map(typedHPExpr)
    val typedTArgs = typeTree.tp.map(typedTypeTree)

    execTyped(typedHArgs, typedTArgs) match {
      case Right(tree) => tree
      case Left(err) =>
        global.repo.error.append(err)
        val prefix = typeTree.expr.setTpe(Type.ErrorType).setSymbol(Symbol.ErrorSymbol)

        TypeTree(prefix, typedHArgs, typedTArgs)
          .setTpe(Type.ErrorType)
          .setSymbol(Symbol.ErrorSymbol)
          .setID(typeTree.id)
    }
  }

  def typedBitLiteral(bit: BitLiteral)(implicit ctx: Context.NodeContext, global: GlobalData): BitLiteral = {
    val length = IntLiteral(bit.length).setTpe(Type.numTpe)
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
      case _ => global.repo.error.append(Error.FinishOutsideStage)
    }

    finish.setTpe(Type.unitTpe).setID(finish.id)
  }

  def typedGoto(goto: Goto)(implicit ctx: Context.NodeContext, global: GlobalData): Goto = {
    val symbol = ctx.owner match {
      case _: Symbol.StateSymbol =>
        ctx.lookup[Symbol.StateSymbol](goto.target) match {
          case LookupResult.LookupSuccess(symbol) => symbol
          case LookupResult.LookupFailure(err) =>
            global.repo.error.append(err)
            Symbol.ErrorSymbol
        }
      case _ =>
        global.repo.error.append(Error.GotoOutsideState)
        Symbol.ErrorSymbol
    }

    goto.setSymbol(symbol).setTpe(Type.unitTpe).setID(goto.id)
  }

  def typedGenerate(generate: Generate)(implicit ctx: Context.NodeContext, global: GlobalData): Generate = {
    val self = ctx.self.getOrElse(throw new ImplementationErrorException("stage must be in module instance"))
    val typedArgs = generate.params.map(typedExpr)

    val (symbol, tpe) =
      if(typedArgs.exists(_.tpe.isErrorType)) (Symbol.ErrorSymbol, Type.ErrorType)
      else self.lookupStage(generate.target, typedArgs.map(_.tpe.asRefType), ctx.hpBounds, ctx.tpBounds) match {
        case LookupResult.LookupFailure(err) =>
          global.repo.error.append(err)
          (Symbol.ErrorSymbol, Type.ErrorType)
        case LookupResult.LookupSuccess((stageSymbol, stageType)) =>
          (stageSymbol, stageType.returnType)
      }

    Generate(generate.target, typedArgs)
      .setSymbol(symbol)
      .setTpe(tpe)
      .setID(generate.id)
  }

  def typedRelay(relay: Relay)(implicit ctx: Context.NodeContext, global: GlobalData): Relay = {
    def verifyRelayTarget: Relay = {
      val self = ctx.self.getOrElse(throw new ImplementationErrorException("stage must be in module instance"))
      val typedArgs = relay.params.map(typedExpr)

      val (symbol, tpe) =
        if(typedArgs.exists(_.tpe.isErrorType)) (Symbol.ErrorSymbol, Type.ErrorType)
        else {
          self.lookupStage(relay.target, typedArgs.map(_.tpe.asRefType), ctx.hpBounds, ctx.tpBounds) match {
            case LookupResult.LookupSuccess((symbol, tpe)) => (symbol, tpe.returnType)
            case LookupResult.LookupFailure(err) =>
              global.repo.error.append(err)
              (Symbol.ErrorSymbol, Type.ErrorType)
          }
        }

      Relay(relay.target, typedArgs).setSymbol(symbol).setTpe(tpe).setID(relay.id)
    }

    ctx.owner match {
      case _: Symbol.StageSymbol => verifyRelayTarget
      case _: Symbol.StateSymbol => verifyRelayTarget
      case _ =>
        global.repo.error.append(Error.RelayOutsideStage)
        relay.setSymbol(Symbol.ErrorSymbol).setTpe(Type.ErrorType)
    }
  }

  def typedReturn(ret: Return)(implicit ctx: Context.NodeContext, global: GlobalData): Return = {
    def typecheck(stage: Symbol.StageSymbol, expr: Expression): Either[Error, Unit] = {
      val retTpe = stage.tpe.asMethodType.returnType

      expr.tpe match {
        case Type.ErrorType => Left(Error.DummyError)
        case tpe: Type.RefType =>
          if(tpe == retTpe) Right(())
          else Left(Error.TypeMismatch(tpe, retTpe))
      }
    }

    val typedRetExpr = typedExpr(ret.expr)

    val result = ctx.owner match {
      case stage: Symbol.StageSymbol =>
        typecheck(stage, typedRetExpr)
      case _: Symbol.StateSymbol =>
        val stage = ctx.owners(1).asInstanceOf[Symbol.StageSymbol]
        typecheck(stage, typedRetExpr)
      case _ =>
        Left(Error.ReturnOutsideStage)
    }

    result.left.foreach(global.repo.error.append)
    Return(typedRetExpr).setTpe(Type.unitTpe).setID(ret.id)
  }

  def typedHPExpr(expr: HPExpr)(implicit ctx: Context.NodeContext, global: GlobalData): HPExpr = expr match {
    case ident: Ident => typedHPIdent(ident)
    case binop: HPBinOp => typedHPBinOp(binop)
    case literal: IntLiteral => typedHPIntLit(literal)
    case literal: StringLiteral => typedHPStrLit(literal)
  }

  def typedHPIdent(ident: Ident)(implicit ctx: Context.NodeContext, global: GlobalData): Ident = {
    def verifyType(symbol: Symbol): Either[Error, Unit] = symbol.tpe match {
      case Type.ErrorType => Left(Error.DummyError)
      case tpe: Type.RefType if tpe =:= Type.numTpe => Right(())
      case tpe: Type.RefType if tpe =:= Type.strTpe => Right(())
      case tpe: Type.RefType => Left(Error.RequireSpecificType(tpe, Type.numTpe, Type.strTpe))
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
    val typedLeft  = typedHPExpr(binop.left)
    val typedRight = typedHPExpr(binop.right)

    val isValid = (typedLeft.tpe =:= Type.numTpe) && (typedRight.tpe =:= Type.numTpe)
    val hasStrTpe = (typedLeft.tpe =:= Type.strTpe) || (typedRight.tpe =:= Type.strTpe)
    val tpe =
      if(isValid) Type.numTpe
      else if(hasStrTpe) { global.repo.error.append(Error.SymbolNotFound("+")); Type.ErrorType }
      else Type.ErrorType

    HPBinOp(binop.op, typedLeft, typedRight).setTpe(tpe).setID(binop.id)
  }

  def typedHPIntLit(int: IntLiteral)(implicit global: GlobalData): IntLiteral = {
    int.setTpe(Type.numTpe)
  }

  def typedHPStrLit(str: StringLiteral)(implicit global: GlobalData): StringLiteral = {
    str.setTpe(Type.strTpe)
  }

  def verifyParamTypes(expect: Vector[Type], actual: Vector[Type])(implicit ctx: Context.NodeContext, global: GlobalData): Vector[Error] = {
    if (expect.length != actual.length)
      return Vector(Error.ParameterLengthMismatch(expect.length, actual.length))

    (expect zip actual)
      .collect { case (e: Type.RefType, a: Type.RefType) => (e, a) }
      .filter { case (e, a) => a =:= e }
      .map { case (e, a) => Error.TypeMismatch(e, a) }
  }

  def typedTypeParam(tpeDef: TypeDef)(implicit ctx: Context.NodeContext, global: GlobalData): TypeDef = {
    Namer.nodeLevelNamed(tpeDef)

    tpeDef.symbol.tpe

    val typedTpeDef = tpeDef.copy(tpeDef.name)
      .setSymbol(tpeDef.symbol)
      .setID(tpeDef.id)

    global.cache.set(typedTpeDef)
    typedTpeDef
  }
}