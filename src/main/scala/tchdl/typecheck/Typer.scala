package tchdl.typecheck

import tchdl.ast._
import tchdl.util.TchdlException.ImplementationErrorException
import tchdl.util._

object Typer {
  def exec(cu: CompilationUnit)(implicit global: GlobalData): CompilationUnit = {
    implicit val ctx = getContext(cu.pkgName, cu.filename.get)

    val topDefs = cu.topDefs.map(diveIntoExpr)

    CompilationUnit(cu.filename, cu.pkgName, cu.imports, topDefs)
  }

  def diveIntoExpr(defTree: Definition)(implicit ctx: Context.RootContext, global: GlobalData): Definition = {
    def extractExprFromMethod(method: MethodDef): Block =
      method.blk
        .getOrElse(throw new ImplementationErrorException("methods in impl should have their body"))


    defTree match {
      case impl: ImplementClass =>
        val implSymbol = impl.symbol.asImplementSymbol
        val implSigCtx = Context(ctx, implSymbol)
        implSigCtx.reAppend(implSymbol.hps ++ implSymbol.tps: _*)

        val implBodyCtx = Context(implSigCtx, impl.target.tpe.asRefType)

        val typedMethods = impl.methods.map { methodDef =>
          val method = methodDef.symbol.asMethodSymbol
          val methodSigCtx = Context(implBodyCtx, method)
          methodSigCtx.reAppend(method.hps ++ method.tps ++ methodDef.params.map(_.symbol.asVariableSymbol): _*)

          val body = extractExprFromMethod(methodDef)
          val typedBody = typedBlock(body)(methodSigCtx, global)

          methodDef.copy(blk = Some(typedBody)).setSymbol(methodDef.symbol).setID(methodDef.id)
        }

        val typedStages = impl.stages.map { stageDef =>
          val stage = stageDef.symbol.asStageSymbol
          val stageSigCtx = Context(implBodyCtx, stage)
          stageSigCtx.reAppend(stageDef.params.map(_.symbol.asVariableSymbol): _*)

          val stageBodyCtx = Context(stageSigCtx)
          stageDef.states.foreach(Namer.namedStateDef(_)(stageBodyCtx, global))
          stageDef.blk.collect{ case vdef: ValDef => vdef }.foreach(Namer.namedValDef(_)(stageBodyCtx, global))

          val typedStates = stageDef.states.map(typedStateDef(_)(stageBodyCtx, global))
          val typedBodyElems = stageDef.blk.map {
            case vdef: ValDef => typedExprValDef(vdef)(stageBodyCtx, global)
            case expr: Expression => typedExpr(expr)(stageBodyCtx, global)
          }

          stageDef.copy(states = typedStates, blk = typedBodyElems).setSymbol(stageDef.symbol.asStageSymbol).setID(stageDef.id)
        }

        impl.copy(methods = typedMethods, stages = typedStages).setSymbol(impl.symbol).setID(impl.id)
      case impl: ImplementInterface =>
        val implSymbol = impl.symbol.asImplementSymbol
        val implSigCtx = Context(ctx, implSymbol)
        implSigCtx.reAppend(implSymbol.hps ++ implSymbol.tps: _*)

        val implBodyCtx = Context(implSigCtx, impl.target.tpe.asRefType)

        val typedMethods = impl.methods.map { methodDef =>
          val method = methodDef.symbol.asMethodSymbol
          val methodSigCtx = Context(implBodyCtx, method)
          methodSigCtx.reAppend(method.hps ++ method.tps ++ methodDef.params.map(_.symbol.asVariableSymbol): _*)

          val body = extractExprFromMethod(methodDef)
          val typedBody = typedBlock(body)(methodSigCtx, global)

          methodDef.copy(blk = Some(typedBody)).setSymbol(methodDef.symbol).setID(methodDef.id)
        }

        impl.copy(methods = typedMethods).setSymbol(impl.symbol).setID(impl.id)
      case others => others
    }
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
    val ttree = vdef.tpeTree.map(typedTypeTree)
    val expr = vdef.expr.map(typedExpr)

    ttree.foreach(global.cache.set)
    expr.foreach(global.cache.set)

    vdef.copy(tpeTree = ttree, expr = expr)
      .setSymbol(vdef.symbol)
      .setID(vdef.id)
  }

  def typedExprValDef(vdef: ValDef)(implicit ctx: Context.NodeContext, global: GlobalData): ValDef = {
    Namer.namedValDef(vdef)

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
          case exprTpe: Type.RefType if exprTpe =!= vdefTpe => Left(Error.TypeMissMatch(vdefTpe, exprTpe))
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
      case binop: BinOp => typedBinOp(binop)
      case ifExpr: IfExpr => typedIfExpr(ifExpr)
      case self: This => typedThis(self)
      case blk: Block => typedBlock(blk)
      case construct: Construct => ???
      case int: IntLiteral => typedIntLiteral(int)
      case string: StringLiteral => typedStringLiteral(string)
      case unit: UnitLiteral => typedUnitLiteral(unit)
      case bit: BitLiteral => typedBitLiteral(bit)
      case apply: Apply => typedExprApply(apply)
      case generate: Generate => typedGenerate(generate)
      case goto: Goto => typedGoto(goto)
      case finish: Finish => typedFinish(finish)
      case relay: Relay => typedRelay(relay)
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
            else Left(Error.TypeMissMatch(p, a))
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

      ctx.lookupLocal[Symbol.MethodSymbol](ident.name) match {
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

    def lookupMethodForSelect(select: Select): Either[Error, Apply] = {
      def verifyPrefixType(tpe: Type): Either[Error, Type.RefType] = tpe match {
        case Type.ErrorType => Left(Error.DummyError)
        case tpe: Type.RefType => Right(tpe)
      }

      def lookup(prefixTpe: Type.RefType): Either[Error, (Symbol.MethodSymbol, Type.MethodType)] = {
        val method = prefixTpe.lookupMethod(
          select.name,
          typedHPs,
          typedTPs.map(_.tpe.asRefType),
          typedArgs.map(_.tpe.asRefType),
          ctx.hpBounds,
          ctx.tpBounds,
          ctx
        )

        method.toEither
      }

      val typedPrefix = typedExpr(select.prefix)

      for {
        prefixTpe <- verifyPrefixType(typedPrefix.tpe)
        result <- lookup(prefixTpe)
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

    if(hasError) errorApply
    else {
      val result = apply.prefix match {
        case ident: Ident => lookupMethodForIdent(ident)
        case select: Select => lookupMethodForSelect(select)
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
        refTpe.lookupField(select.name) match {
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

  def typedBinOp(binop: BinOp)(implicit ctx: Context.NodeContext, global: GlobalData): BinOp = {
    val typedLeft = typedExpr(binop.left)
    val typedRight = typedExpr(binop.right)

    val result = (typedLeft.tpe, typedRight.tpe) match {
      case (Type.ErrorType, _) => LookupResult.LookupFailure(Error.DummyError)
      case (_, Type.ErrorType) => LookupResult.LookupFailure(Error.DummyError)
      case (leftTpe: Type.RefType, rightTpe: Type.RefType) =>
        leftTpe.lookupOperator(binop.op, rightTpe)
    }

    result match {
      case LookupResult.LookupFailure(err) =>
        global.repo.error.append(err)
        binop.setSymbol(Symbol.ErrorSymbol).setTpe(Type.ErrorType)
      case LookupResult.LookupSuccess((methodSymbol, methodTpe)) =>
        binop.setSymbol(methodSymbol).setTpe(methodTpe.returnType)
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
    ctx.self match {
      case None =>
        global.repo.error.append(Error.UsingSelfOutsideClass)
        This().setTpe(Type.ErrorType).setID(self.id)
      case Some(tpe) =>
        This().setTpe(tpe).setID(self.id)
    }
  }

  def typedIfExpr(ifexpr: IfExpr)(implicit ctx: Context.NodeContext, global: GlobalData): IfExpr = {
    val typedCond = typedExpr(ifexpr.cond)
    val typedConseq = typedExpr(ifexpr.conseq)
    val typedAlt = ifexpr.alt.map(typedExpr)

    def isBoolTpe = typedCond.tpe != Type.boolTpe
    def isBit1Tpe = typedCond.tpe != Type.bitTpe(IntLiteral(1))
    def isErrorTpe = typedCond.tpe.isErrorType
    if (!isBoolTpe && !isBit1Tpe && !isErrorTpe)
      global.repo.error.append(Error.RequireSpecificType(typedCond.tpe.asRefType, Type.boolTpe, Type.bitTpe(IntLiteral(1))))

    typedAlt match {
      case None =>
        IfExpr(typedCond, typedConseq, typedAlt).setTpe(Type.unitTpe).setID(ifexpr.id)
      case Some(alt) =>
        val retTpe = (alt.tpe, typedConseq.tpe) match {
          case (Type.ErrorType, tpe) => tpe
          case (tpe, Type.ErrorType) => tpe
          case (altTpe, conseqTpe)  =>
            if(altTpe =!= conseqTpe)
              global.repo.error.append(Error.TypeMissMatch(altTpe, conseqTpe))

            altTpe
        }

        IfExpr(typedCond, typedConseq, typedAlt).setTpe(retTpe).setID(ifexpr.id)
    }
  }

  def typedTypeTree(typeTree: TypeTree)(implicit ctx: Context.NodeContext, global: GlobalData): TypeTree = {
    val TypeTree(Ident(name), hps, tps) = typeTree

    def error(hps: Vector[HPExpr], tps: Vector[TypeTree]) =
      TypeTree(Ident(name), hps, tps)
        .setTpe(Type.ErrorType)
        .setSymbol(Symbol.ErrorSymbol)
        .setID(typeTree.id)

    def verifyHP(symbol: Symbol.TypeSymbol, typedHPs: Vector[HPExpr]): Either[Error, Unit] = {
      val invalidHPLength = symbol.hps.length != typedHPs.length
      val hasError = typedHPs.exists(_.tpe.isErrorType)

      if(invalidHPLength) Left(Error.HardParameterLengthMismatch(symbol.hps.length, hps.length))
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

    ctx.lookup[Symbol.TypeSymbol](name) match {
      case LookupResult.LookupFailure(err) =>
        global.repo.error.append(err)
        error(hps, tps)
      case LookupResult.LookupSuccess(symbol) =>
        val typedHPs = hps.map(typedHPExpr)
        val typedTPs = tps.map(typedTypeTree)

        val result = for {
          _ <- verifyHP(symbol, typedHPs)
          _ <- verifyTP(symbol, typedHPs, typedTPs)
        } yield ()

        result match {
          case Left(err) =>
            global.repo.error.append(err)
            error(typedHPs, typedTPs)
          case Right(()) =>
            TypeTree(Ident(name), typedHPs, typedTPs)
              .setTpe(Type.RefType(symbol, typedHPs, typedTPs.map(_.tpe.asRefType)))
              .setSymbol(symbol)
              .setID(typeTree.id)
        }
    }
  }

  def typedBitLiteral(bit: BitLiteral)(implicit ctx: Context.NodeContext, global: GlobalData): BitLiteral = {
    val length = IntLiteral(bit.length).setTpe(Type.numTpe)
    val bitTpe = Type.bitTpe(length)

    bit.setTpe(bitTpe).setID(bit.id)
  }

  def typedIntLiteral(int: IntLiteral)(implicit ctx: Context.NodeContext, global: GlobalData): IntLiteral = {
    int.setTpe(Type.intTpe).setID(int.id)
  }

  def typedUnitLiteral(unit: UnitLiteral)(implicit ctx: Context.NodeContext, global: GlobalData): UnitLiteral = {
    unit.setTpe(Type.unitTpe).setID(unit.id)
  }

  def typedStringLiteral(str: StringLiteral)(implicit ctx: Context.NodeContext, global: GlobalData): StringLiteral = {
    str.setTpe(Type.strTpe).setID(str.id)
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
    ctx.owner match {
      case _: Symbol.StateSymbol =>
        ctx.lookup[Symbol.StateSymbol](goto.target) match {
          case LookupResult.LookupFailure(err) => global.repo.error.append(err)
          case _ =>
        }
      case _ => global.repo.error.append(Error.GotoOutsideState)
    }

    goto.setTpe(Type.unitTpe).setID(goto.id)
  }

  def typedGenerate(generate: Generate)(implicit ctx: Context.NodeContext, global: GlobalData): Generate = {
    val tpe = ctx.lookup[Symbol.StageSymbol](generate.target) match {
      case LookupResult.LookupFailure(err) =>
        global.repo.error.append(err)
        Type.ErrorType
      case LookupResult.LookupSuccess(symbol) =>
        val tpe = symbol.tpe.asMethodType
        val typedArgs = generate.params.map(typedExpr)

        verifyParamTypes(tpe.params, typedArgs.map(_.tpe)).foreach(global.repo.error.append)
        tpe.returnType
    }

    generate.setTpe(tpe)
  }

  def typedRelay(relay: Relay)(implicit ctx: Context.NodeContext, global: GlobalData): Relay = {
    ctx.owner match {
      case _: Symbol.StageSymbol =>
      case _: Symbol.StateSymbol =>
      case _ => global.repo.error.append(Error.RelayOutsideStage)
    }

    val tpe = ctx.lookup[Symbol.StageSymbol](relay.target) match {
      case LookupResult.LookupFailure(err) =>
        global.repo.error.append(err)
        Type.ErrorType
      case LookupResult.LookupSuccess(symbol) =>
        val tpe = symbol.tpe.asMethodType
        val typedArgs = relay.params.map(typedExpr)

        verifyParamTypes(tpe.params, typedArgs.map(_.tpe)).foreach(global.repo.error.append)

        tpe.returnType
    }

    relay.setTpe(tpe)
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
      .map { case (e, a) => Error.TypeMissMatch(e, a) }
  }

  def typedTypeParam(tpeDef: TypeDef)(implicit ctx: Context.NodeContext, global: GlobalData): TypeDef = {
    Namer.nodeLevelNamed(tpeDef, ctx)

    tpeDef.symbol.tpe

    val typedTpeDef = tpeDef.copy(tpeDef.name)
      .setSymbol(tpeDef.symbol)
      .setID(tpeDef.id)

    global.cache.set(typedTpeDef)
    typedTpeDef
  }

  /*
  def verifyTypeParams(
    symbol: Symbol.TypeSymbol,
    hps: Vector[HPExpr],
    tps: Vector[TypeTree],
    tpe: Type.EntityType
  )(
    implicit ctx: Context.NodeContext,
  ): TypeTree = {
    val actualLength = hps.length + tps.length
    val expectLength = tpe.hardwareParam.length + tpe.typeParam.length

    if (expectLength != actualLength) {
      Reporter.appendError(Error.ParameterLengthMismatch(expectLength, actualLength))

      return TypeTree(Ident(symbol.name), hps, tps).setTpe(Type.ErrorType).setSymbol(Symbol.ErrorSymbol)
    }

    val (splitHps, tpsFrontHalf) = hps.splitAt(tpe.hardwareParam.length)

    val typedHps = splitHps.map(typedHardwareParamExpr)
    val typedTpsFrontHalf = tpsFrontHalf.map(typedType)
    val typedTpsLatterHalf = tps.map(typedTypeTree(_)(ctx, acceptPkg = false))
    val typedTps = typedTpsFrontHalf ++ typedTpsLatterHalf

    val (treeTpe, treeSymbol) =
      if (typedHps.exists(_.tpe.isErrorType) || typedTps.exists(_.tpe.isErrorType))
        (Type.ErrorType, Symbol.ErrorSymbol)
      else
        (Type.RefType(symbol, typedHps, typedTps.map(_.tpe.asRefType)), symbol)

    TypeTree(Ident(symbol.name), typedHps, typedTps).setTpe(treeTpe).setSymbol(treeSymbol)
  }
   */
}

object TyperForTopDefinition {
  def exec(cu: CompilationUnit)(implicit global: GlobalData): CompilationUnit = {
    val ctx = global.rootPackage.search(cu.pkgName)
      .getOrElse(throw new ImplementationErrorException(s"${cu.pkgName} should be there"))
      .lookupCtx(cu.filename.get)
      .getOrElse(throw new ImplementationErrorException(s"${cu.filename.get}'s context should be there'"))

    // val typedTopDefs = cu.topDefs.map()
    ???
  }

  def typedTopDefs(defTree: Definition)(implicit ctx: Context.RootContext, global: GlobalData): Definition =
    defTree match {
      case struct: StructDef => typedStructDef(struct)
    }

  def typedStructDef(struct: StructDef)(implicit ctx: Context.RootContext, global: GlobalData): StructDef = {
    /*
    struct.symbol.tpe

    val signatureCtx = Context(ctx, struct.symbol)
    ctx.reAppend(
      struct.hp.map(_.symbol) ++
      struct.tp.map(_.symbol): _*
    )

    val typedHp = struct.hp.map(typedValDef(_)(signatureCtx, global))
    val typedTp = struct.tp.map(Typer.typedTypeParam(_)(signatureCtx, global))

    val fieldCtx = Context(signatureCtx)
    fieldCtx.reAppend(struct.fields.map(_.symbol): _*)
    val typedFields = struct.fields.map(typedValDef(_)(fieldCtx, global))

    val typedStruct = struct.copy(
      struct.name,
      typedHp,
      typedTp,
      struct.bounds,
      typedFields
    )
      .setSymbol(struct.symbol)
      .setID(struct.id)

    global.cache.set(typedStruct)
    typedStruct

     */
    ???
  }

  def typedModuleDef(moduleDef: ModuleDef)(implicit ctx: Context.RootContext, global: GlobalData): ModuleDef = {
    ???
  }

  def typedInterfaceDef(interfaceDef: InterfaceDef)(implicit ctx: Context.RootContext, global: GlobalData): InterfaceDef = {
    ???
  }


}
