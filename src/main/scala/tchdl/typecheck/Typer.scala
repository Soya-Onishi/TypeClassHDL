package tchdl.typecheck

import tchdl.ast._
import tchdl.util.TchdlException.ImplimentationErrorException
import tchdl.util.{Context, Error, Symbol, Type}

object Typer {
  def exec(cu: CompilationUnit): CompilationUnit = {
    ???
  }

  def typedDefinition(
      definition: Definition
  )(implicit ctx: Context): Definition = definition match {
    case typeDef: TypeDef  => typedTypeDef(typeDef)
    case valDef: ValDef    => typedValDef(valDef)
    case state: StateDef   => typedStateDef(state)
    case always: AlwaysDef => typedAlwaysDef(always)
    case module: ModuleDef => typedModuleDef(module)
    case struct: StructDef => typedStructDef(struct)
    case stage: StageDef   => typedStageDef(stage)
    case method: MethodDef => typedMethodDef(method)
  }

  def typedModuleDef(module: ModuleDef)(implicit ctx: Context): ModuleDef = {
    module.symbol.tpe

    val interfaceCtx = Context(ctx, module.name, module.symbol)
    val typedHp = module.hp.map(typedValDef(_)(interfaceCtx))
    val typedTp = module.tp.map(typedTypeDef(_)(interfaceCtx))
    module.bounds.foreach(typedBound(_)(interfaceCtx))
    val typedParents = module.parents.map(typedValDef(_)(interfaceCtx))
    val typedSiblings = module.siblings.map(typedValDef(_)(interfaceCtx))

    val componentCtx = Context(interfaceCtx)
    val typedComponents =
      module.components.map(typedDefinition(_)(componentCtx))

    module.copy(
      module.name,
      typedHp,
      typedTp,
      module.bounds,
      typedParents,
      typedSiblings,
      typedComponents.map(_.asInstanceOf[Component])
    )
  }

  def typedStructDef(struct: StructDef)(implicit ctx: Context): StructDef = {
    struct.symbol.tpe

    val interfaceCtx = Context(ctx, struct.name, struct.symbol)
    ctx.reAppend(
      struct.hp.map(_.symbol) ++
        struct.tp.map(_.symbol): _*
    )

    val typedHp = struct.hp.map(typedValDef(_)(interfaceCtx))
    val typedTp = struct.tp.map(typedTypeDef(_)(interfaceCtx))
    struct.bounds.foreach(typedBound(_)(interfaceCtx))

    val fieldCtx = Context(interfaceCtx)
    fieldCtx.reAppend(struct.fields.map(_.symbol): _*)
    val typedFields = struct.fields.map(typedValDef(_)(fieldCtx))

    struct.copy(
      struct.name,
      typedHp,
      typedTp,
      struct.bounds,
      typedFields
    )
  }

  def typedAlwaysDef(always: AlwaysDef)(implicit ctx: Context): AlwaysDef = {
    val alwaysCtx = Context(ctx, always.name, always.symbol)
    val typedBlk = typedBlock(always.blk)(alwaysCtx)

    always.copy(
      always.name,
      typedBlk
    )
  }

  def typedMethodDef(method: MethodDef)(implicit ctx: Context): MethodDef = {
    method.symbol.tpe

    val signatureCtx = Context(ctx, method.name, method.symbol)
    ctx.reAppend(
      method.hp.map(_.symbol) ++
        method.tp.map(_.symbol) ++
        method.params.map(_.symbol): _*
    )

    val typedHp = method.hp.map(typedValDef(_)(signatureCtx))
    val typedTp = method.tp.map(typedTypeDef(_)(signatureCtx))
    method.bounds.foreach(typedBound(_)(signatureCtx))
    val typedParams = method.params.map(typedValDef(_)(signatureCtx))
    val typedRetTpe = typedTypeTree(method.retTpe)(signatureCtx)
    val typedBlk = method.blk.map(typedBlock(_)(signatureCtx))

    method.copy(
      method.name,
      typedHp,
      typedTp,
      method.bounds,
      typedParams,
      typedRetTpe,
      typedBlk
    )
  }

  def typedValDef(vdef: ValDef)(implicit ctx: Context): ValDef = {
    vdef.symbol.tpe

    val typedTpeTree = vdef.tpeTree.map(typedTypeTree)
    val typedExp = vdef.expr.map(typedExpr)

    vdef.copy(
      tpeTree = typedTpeTree,
      expr = typedExp
    )
  }

  def typedStageDef(stage: StageDef)(implicit ctx: Context): StageDef = {
    stage.symbol.tpe

    val signatureCtx = Context(ctx, stage.name, stage.symbol)
    ctx.reAppend(stage.params.map(_.symbol): _*)

    val typedParams = stage.params.map(typedValDef(_)(signatureCtx))
    val typedRetTpe = typedTypeTree(stage.retTpe)(signatureCtx)

    val blkCtx = Context(signatureCtx)
    stage.blk.map(Namer.named(_, blkCtx))
    stage.states.map(Namer.named(_, blkCtx))

    val typedBlkElems = stage.blk.map {
      case vdef: ValDef     => typedValDef(vdef)(blkCtx)
      case expr: Expression => typedExpr(expr)(blkCtx)
    }

    val typedStates = stage.states.map(typedStateDef(_)(blkCtx))

    stage.copy(
      stage.name,
      typedParams,
      typedRetTpe,
      typedStates,
      typedBlkElems
    )
  }

  def typedStateDef(state: StateDef)(implicit ctx: Context): StateDef = {
    val stateCtx = Context(ctx, state.name, state.symbol)
    val typedBlk = typedBlock(state.blk)(stateCtx)

    state.copy(state.name, typedBlk)
  }

  def typedTypeDef(tpeDef: TypeDef)(implicit ctx: Context): TypeDef = {
    Namer.named(tpeDef, ctx)

    tpeDef.symbol.tpe

    tpeDef.copy(tpeDef.name)
  }

  def typedBound(bound: Bound)(implicit ctx: Context): Unit = {
    ctx.lookup(bound.target) match {
      case Left(err) => ctx.appendError(err)
      case Right(symbol: Symbol.TypeParamSymbol) =>
        ctx.owner match {
          case None =>
            throw new ImplimentationErrorException(
              "Context should have owner, but there is no one"
            )
          case Some(owner) if symbol.owner != owner =>
            val err = Error.SetBoundForDifferentOwner(owner, symbol.owner)
            ctx.appendError(err)
          case Some(_) =>
            val typedTT = bound.constraints.map(typedTypeTree)
            if (!typedTT.exists(_.tpe.isErrorType)) {
              symbol.tpe.asParameterType
                  .appendConstraints(typedTT.map(_.tpe.asRefType))
            }
        }
      case Right(symbol) =>
        val err = Error.RequireTypeParamSymbol(symbol.name)
        ctx.appendError(err)
    }
  }

  def typedExpr(expr: Expression)(implicit ctx: Context): Expression =
    expr match {
      case ident: Ident          => typedExprIdent(ident)
      case select: Select        => typedExprSelect(select)
      case ifExpr: IfExpr        => typedIfExpr(ifExpr)
      case _: Self               => typedSelf
      case blk: Block            => typedBlock(blk)
      case construct: Construct  => ???
      case int: IntLiteral       => typedIntLiteral(int)
      case string: StringLiteral => typedStringLiteral(string)
      case unit: UnitLiteral     => typedUnitLiteral(unit)
      case bit: BitLiteral       => typedBitLiteral(bit)
      case _: Apply =>
        throw new ImplimentationErrorException("Apply tree should not be typed")
      case applyParams: ApplyParams => typedExprApplyParams(applyParams)
      case _: ApplyTypeParams =>
        throw new ImplimentationErrorException(
          "ApplyTypeParam tree should be handled in typedExprApplyParams"
        )
      case generate: Generate => typedGenerate(generate)
      case goto: Goto         => typedGoto(goto)
      case finish: Finish     => typedFinish(finish)
      case relay: Relay       => typedRelay(relay)
    }

  def typedExprIdent(ident: Ident)(implicit ctx: Context): Ident = {
    ctx.lookup(ident.name) match {
      case Left(err) =>
        ctx.appendError(err)
        ident.setTpe(Type.ErrorType)
      case Right(symbol: Symbol.TypeSymbol) =>
        ctx.appendError(Error.SymbolIsType(symbol.name))
        ident.setTpe(Type.ErrorType).setSymbol(Symbol.ErrorSymbol)
      case Right(symbol: Symbol.TermSymbol) =>
        ident.setTpe(symbol.tpe.asRefType).setSymbol(symbol)
    }
  }

  def typedExprApplyParams(apply: ApplyParams)(implicit ctx: Context): Apply = {
    apply.suffix match {
      case applyTPs: ApplyTypeParams =>
        typedExprApplyTypeParams(applyTPs) match {
          case Left(errs) =>
            errs.foreach(ctx.appendError)
            Apply(applyTPs.suffix, Vector.empty, Vector.empty, Vector.empty)
              .setTpe(Type.ErrorType)
          case Right((suffix, hps, tps)) =>
            val methodTpe = suffix.tpe.asMethodType
            val typedArgs = apply.args.map(typedExpr)
            val typeParamMap =
              (methodTpe.typeParam zip tps).map {
                case (sym, tp) => sym -> tp.tpe.asRefType
              }.toMap

            val replacedArgTpes =
              methodTpe.params.map(_.replaceWithTypeParamMap(typeParamMap))

            val errors = verifyTypes(replacedArgTpes, typedArgs.map(_.tpe))
            val retTpe =
              if (errors.nonEmpty) Type.ErrorType
              else methodTpe.returnType.replaceWithTypeParamMap(typeParamMap)

            Apply(suffix, hps, tps, typedArgs).setTpe(retTpe)
        }
      case expr: Expression =>
        val typedExp = typedExpr(expr)
        typedExp.tpe match {
          case methodTpe: Type.MethodType
              if methodTpe.hardwareParam.nonEmpty || methodTpe.typeParam.nonEmpty =>
            // For now, if method type has type parameter or hardware parameter,
            // user must write type parameter and hardware parameter explicitly.
            ctx.appendError(Error.RequireTypeParameter)
            Apply(typedExp, Vector.empty, Vector.empty, Vector.empty)
              .setTpe(Type.ErrorType)
          case methodTpe: Type.MethodType =>
            val typedArgs = apply.args.map(typedExpr)

            val errors = verifyTypes(methodTpe.params, typedArgs.map(_.tpe))
            errors.foreach(ctx.appendError)

            val returnType =
              if (errors.isEmpty) methodTpe.returnType
              else Type.ErrorType

            Apply(typedExp, Vector.empty, Vector.empty, typedArgs)
              .setTpe(returnType)
        }
    }
  }

  def typedExprApplyTypeParams(apply: ApplyTypeParams)(
      implicit ctx: Context
  ): Either[Vector[Error], (Expression, Vector[Expression], Vector[TypeTree])] = {
    val typedSuffix = typedExpr(apply.suffix)
    typedSuffix.tpe match {
      case method: Type.MethodType =>
        if (method.typeParam.isEmpty && method.hardwareParam.isEmpty)
          Left(Vector(Error.NoNeedTypeParameter(method)))
        else if (method.typeParam.length + method.hardwareParam.length != apply.tp.length) {
          val expect = method.typeParam.length + method.hardwareParam.length
          val actual = apply.tp.length
          val err = Error.ParameterLengthMismatch(expect, actual)
          Left(Vector(err))
        } else {
          val (hps, tps) = apply.tp.splitAt(method.typeParam.length)
          val typedHps = hps.map(typedExpr)
          val typedTps = tps.map(typedType)

          val mismatchHpTypes =
            (typedHps.map(_.tpe) zip method.hardwareParam.map(_.tpe))
              .filter { case (actual, expect) => actual != expect }
              .map {
                case (actual, expect) => Error.TypeMissmatch(actual, expect)
              }

          val mismatchTpBounds =
            (typedTps.map(_.tpe) zip method.typeParam)
              .filter {
                case (actual, tp) => ??? /* TODO: check whether passed type meet bound restriction */
              }
              .map { case (actual, tp) => ??? }

          val errs = mismatchHpTypes ++ mismatchTpBounds

          if (errs.nonEmpty) Left(errs)
          else Right((typedSuffix, typedHps, typedTps))
        }
      case tpe => Left(Vector(Error.RequireMethodType(tpe)))
    }
  }

  def typedExprSelect(select: Select)(implicit ctx: Context): Select = {
    val typedSuffix = typedExpr(select.expr)
    typedSuffix.tpe match {
      case refTpe: Type.RefType =>
        refTpe.lookup(select.name) match {
          case Left(err) =>
            ctx.appendError(err)
            Select(typedSuffix, select.name).setTpe(Type.ErrorType)
          case Right(symbol) =>
            val map = {
              val refTpe = typedSuffix.tpe.asRefType

              refTpe.origin.tpe match {
                case _: Type.ParameterType => Map.empty[Symbol.TypeSymbol, Type.RefType]
                case tpe: Type.EntityType =>
                  tpe.typeParam
                    .zip(refTpe.typeParam)
                    .map{ case (sym, tpe) => sym -> tpe }
                    .toMap
              }
            }

            symbol.tpe match {
              case tpe: Type.RefType =>
                val refTpe = tpe.replaceWithTypeParamMap(map)
                Select(typedSuffix, select.name).setTpe(refTpe)
              case tpe: Type.MethodType =>
                val methodTpe = tpe.replaceWithTypeParamMap(map)
                Select(typedSuffix, select.name).setTpe(methodTpe)
            }
        }
    }
  }

  def typedBlock(blk: Block)(implicit ctx: Context): Block = {
    val blkCtx = Context(ctx, ctx.getBlkID.toString)

    val typedElems = blk.elems.map {
      case vdef: ValDef     => typedValDef(vdef)(blkCtx)
      case expr: Expression => typedExpr(expr)(blkCtx)
    }

    val typedLast = typedExpr(blk.last)(blkCtx)

    Block(typedElems, typedLast).setTpe(typedLast.tpe)
  }

  def typedSelf(implicit ctx: Context): Self = {
    ctx.enclosedClass match {
      case None =>
        ctx.appendError(Error.UsingSelfOutsideClass)
        Self().setTpe(Type.ErrorType)
      case Some(symbol) =>
        val tpe = symbol.tpe.asEntityType
        val refTpe = Type.RefType(
          symbol,
          tpe.hardwareParam.map(hp =>
            Ident(hp.name).setTpe(hp.tpe).setSymbol(hp)
          ),
          tpe.typeParam.map(tp => Type.RefType(tp, Vector.empty, Vector.empty))
        )

        Self().setTpe(refTpe)
    }
  }

  def typedIfExpr(ifexpr: IfExpr)(implicit ctx: Context): IfExpr = {
    val typedCond = typedExpr(ifexpr.cond)
    val typedConseq = typedExpr(ifexpr.conseq)
    val typedAlt = ifexpr.alt.map(typedExpr)

    // TODO: check whether typedCond.tpe is Boolean or not
    if (typedCond.tpe != ???)
      ctx.appendError(Error.RequireBooleanType(typedCond.tpe))

    typedAlt match {
      case None =>
        IfExpr(typedCond, typedConseq, typedAlt).setTpe(Type.unitTpe)
      case Some(alt) =>
        if (typedConseq.tpe != alt.tpe)
          ctx.appendError(Error.TypeMissmatch(alt.tpe, typedConseq.tpe))

        val retTpe = (alt.tpe, typedConseq.tpe) match {
          case (Type.ErrorType, tpe) => tpe
          case (tpe, _)              => tpe
        }

        IfExpr(typedCond, typedConseq, typedAlt).setTpe(retTpe)
    }
  }

  def typedType(expr: Expression)(implicit ctx: Context): TypeTree =
    expr match {
      case ident: Ident           => typedTypeIdent(ident)
      case apply: ApplyTypeParams => typedTypeApplyTypeParams(apply)
      case expr                   =>
        // TODO: Add error represents that it is inappropriate AST to represent Type
        ctx.appendError(Error.InvalidFormatForType(expr))
        TypeTree("", Vector.empty, Vector.empty).setTpe(Type.ErrorType)
    }

  def typedTypeIdent(ident: Ident)(implicit ctx: Context): TypeTree = {
    ctx.lookup(ident.name) match {
      case Left(err) =>
        ctx.appendError(err)
        TypeTree(ident.name, Vector.empty, Vector.empty).setTpe(Type.ErrorType)
      case Right(symbol: Symbol.TermSymbol) =>
        ctx.appendError(Error.SymbolIsTerm(symbol.name))
        TypeTree(symbol.name, Vector.empty, Vector.empty).setTpe(Type.ErrorType)
      case Right(symbol: Symbol.TypeSymbol) =>
        /*
         * If a type requires type parameter, this process cause error
         * because this process expect only monomorphic type
         * like Int and String, but not List[_] and Option[_].
         */
        val retTpe = symbol.tpe match {
          case tpe: Type.EntityType if tpe.hardwareParam.nonEmpty || tpe.typeParam.nonEmpty =>
            ctx.appendError(Error.RequireTypeParameter)
            Type.ErrorType
          case _ =>
            Type.RefType(symbol, Vector.empty, Vector.empty)
        }

        TypeTree(symbol.name, Vector.empty, Vector.empty).setTpe(retTpe)
    }
  }

  def typedTypeApplyTypeParams(
      apply: ApplyTypeParams
  )(implicit ctx: Context): TypeTree = {
    val ApplyTypeParams(Ident(name), typeParams) = apply

    ctx.lookup(name) match {
      case Left(err) =>
        ctx.appendError(err)
        TypeTree(name, Vector.empty, Vector.empty).setTpe(Type.ErrorType)
      case Right(symbol: Symbol.TermSymbol) =>
        ctx.appendError(Error.SymbolIsTerm(symbol.name))
        TypeTree(name, Vector.empty, Vector.empty).setTpe(Type.ErrorType)
      case Right(symbol: Symbol.TypeSymbol) =>
        symbol.tpe match {
          case _: Type.ParameterType => ??? // TODO: Parameter type must not have type paramter like A[B]
          case tpe: Type.EntityType =>
            if (typeParams.length != tpe.typeParam.length + tpe.hardwareParam.length) {
              val expect = tpe.typeParam.length + tpe.hardwareParam.length
              val actual = typeParams.length
              ctx.appendError(Error.ParameterLengthMismatch(expect, actual))
              return TypeTree(name, Vector.empty, Vector.empty)
                .setTpe(Type.ErrorType)
            }

            val (hps, tps) = typeParams.splitAt(tpe.hardwareParam.length)
            val typedHps = hps.map(typedExpr)
            val typedTps = tps.map(typedType)

            val typeTreeTpe =
              if (typedHps.exists(_.tpe.isErrorType) || typedTps.exists(
                _.tpe.isErrorType
              )) {
                Type.ErrorType
              } else {
                Type.RefType(symbol, typedHps, typedTps.map(_.tpe.asRefType))
              }

            TypeTree(name, typedHps, typedTps).setTpe(typeTreeTpe)
        }
    }
  }

  def typedTypeTree(typeTree: TypeTree)(implicit ctx: Context): TypeTree = {
    ctx.lookup(typeTree.name) match {
      case Left(err) =>
        ctx.appendError(err)
        typeTree.setTpe(Type.ErrorType)
      case Right(symbol: Symbol.TermSymbol) =>
        ctx.appendError(Error.SymbolIsTerm(symbol.name))
        typeTree.setTpe(Type.ErrorType)
      case Right(symbol: Symbol.TypeSymbol) =>
        symbol.tpe match {
          case tpe: Type.EntityType => verifyTypeParams(typeTree, symbol, tpe)
          case _: Type.ParameterType => ???
        }
    }
  }

  def typedBitLiteral(bit: BitLiteral)(implicit ctx: Context): BitLiteral = {
    val bitSymbol = Symbol.lookupBuiltin("Bit")
    val intSymbol = Symbol.lookupBuiltin("Int32")
    val intTpe = Type.RefType(intSymbol, Vector.empty, Vector.empty)
    val length = IntLiteral(bit.length).setTpe(intTpe)

    val bitTpe = Type.RefType(bitSymbol, Vector(length), Vector.empty)

    bit.setTpe(bitTpe)
  }

  def typedIntLiteral(int: IntLiteral)(implicit ctx: Context): IntLiteral = {
    val intSymbol = Symbol.lookupBuiltin("Int32")
    val intTpe = Type.RefType(intSymbol)

    int.setTpe(intTpe)
  }

  def typedUnitLiteral(
      unit: UnitLiteral
  )(implicit ctx: Context): UnitLiteral = {
    val unitSymbol = Symbol.lookupBuiltin("Unit")
    val unitTpe = Type.RefType(unitSymbol)

    unit.setTpe(unitTpe)
  }

  def typedStringLiteral(
      str: StringLiteral
  )(implicit ctx: Context): StringLiteral = {
    val strSymbol = Symbol.lookupBuiltin("String")
    val strTpe = Type.RefType(strSymbol)

    str.setTpe(strTpe)
  }

  def typedFinish(finish: Finish)(implicit ctx: Context): Finish = {
    ctx.owner match {
      case Some(_: Symbol.StateSymbol) =>
      case Some(_: Symbol.StageSymbol) =>
      case _ =>
        ctx.appendError(Error.FinishOutsideStage)
    }

    finish.setTpe(Type.unitTpe)
  }

  def typedGoto(goto: Goto)(implicit ctx: Context): Goto = {
    ctx.owner match {
      case Some(_: Symbol.StateSymbol) =>
        ctx.lookup(goto.target) match {
          case Left(err)                    => ctx.appendError(err)
          case Right(_: Symbol.StateSymbol) =>
          case Right(symbol) =>
            ctx.appendError(Error.RequireStateSymbol(symbol.name))
        }
      case _ =>
        ctx.appendError(Error.GotoOutsideState)
    }

    goto.setTpe(Type.unitTpe)
  }

  def typedGenerate(generate: Generate)(implicit ctx: Context): Generate = {
    ctx.lookup(generate.target) match {
      case Left(err) =>
        ctx.appendError(err)
        generate.setTpe(Type.ErrorType)
      case Right(symbol: Symbol.StageSymbol) =>
        val tpe = symbol.tpe.asMethodType
        val typedArgs = generate.params.map(typedExpr)

        verifyTypes(tpe.params, typedArgs.map(_.tpe))
          .foreach(ctx.appendError)
        generate.setTpe(tpe.returnType)
      case Right(symbol) =>
        ctx.appendError(Error.RequireStageSymbol(symbol.name))
        generate.setTpe(Type.ErrorType)
    }
  }

  def typedRelay(relay: Relay)(implicit ctx: Context): Relay = {
    ctx.owner match {
      case Some(_: Symbol.StageSymbol) =>
      case Some(_: Symbol.StateSymbol) =>
      case _                           => ctx.appendError(Error.RelayOutsideStage)
    }

    ctx.lookup(relay.target) match {
      case Left(err) =>
        ctx.appendError(err)
        relay.setTpe(Type.ErrorType)
      case Right(symbol: Symbol.StageSymbol) =>
        val tpe = symbol.tpe.asMethodType
        val typedArgs = relay.params.map(typedExpr)

        verifyTypes(tpe.params, typedArgs.map(_.tpe))
          .foreach(ctx.appendError)

        relay.setTpe(tpe.returnType)
      case Right(symbol) =>
        ctx.appendError(Error.RequireStageSymbol(symbol.name))
        relay.setTpe(Type.ErrorType)
    }
  }

  def verifyTypes(expect: Vector[Type], actual: Vector[Type])(
      implicit ctx: Context
  ): Vector[Error] = {
    if (expect.length != actual.length)
      return Vector(Error.ParameterLengthMismatch(expect.length, actual.length))

    (expect zip actual)
      .filter { case (e, a) => e != a }
      .map { case (e, a) => Error.TypeMissmatch(e, a) }
  }

  def verifyType(expect: Type, actual: Type)(
      implicit ctx: Context
  ): Vector[Error] =
    verifyTypes(Vector(expect), Vector(actual))

  def verifyTypeParams(typeTree: TypeTree, symbol: Symbol.TypeSymbol, tpe: Type.EntityType)(implicit ctx: Context): TypeTree = {
    if (typeTree.hp.length != tpe.hardwareParam.length + tpe.typeParam.length) {
      val expect = tpe.hardwareParam.length + tpe.typeParam.length
      val actual = typeTree.hp.length
      ctx.appendError(Error.ParameterLengthMismatch(expect, actual))

      return typeTree.setTpe(Type.ErrorType)
    }

    val (hps, tps) = typeTree.hp.splitAt(tpe.hardwareParam.length)

    val typedHps = hps.map(typedExpr)
    val typedTps = tps.map(typedType)

    val treeTpe =
      if (typedHps.exists(_.tpe.isErrorType) || typedTps.exists(_.tpe.isErrorType))
        Type.ErrorType
      else
        Type.RefType(symbol, typedHps, typedTps.map(_.tpe.asRefType))

    TypeTree(typeTree.name, typedHps, typedTps).setTpe(treeTpe)
  }
}
