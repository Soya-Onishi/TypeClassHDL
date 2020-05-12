package tchdl.typecheck

import tchdl.ast._
import tchdl.util.TchdlException.ImplementationErrorException
import tchdl.util.{Context, Error, LookupResult, Reporter, Symbol, Type}

object Typer {
  def exec(cu: CompilationUnit): CompilationUnit = {
    ???
  }

  def typedTopLevelDefinition(ast: Definition)(implicit ctx: Context.RootContext): Definition = ast match {
    case module: ModuleDef => typedModuleDef(module)
    case struct: StructDef => typedStructDef(struct)
    case implClass: ImplementClass => typedImplementClass(implClass)
    case implInterface: ImplementInterface => typedImplementInterface(implInterface)
    case deftree =>
      val msg = s"typed [${deftree.getClass.getName}] at top level but it is invalid"
      throw new ImplementationErrorException(msg)
  }

  def typedDefinition(ast: Definition)(implicit ctx: Context.NodeContext): Definition = ast match {
    case typeDef: TypeDef => typedTypeDef(typeDef)
    case valDef: ValDef => typedValDef(valDef)
    case state: StateDef => typedStateDef(state)
    case always: AlwaysDef => typedAlwaysDef(always)
    case stage: StageDef => typedStageDef(stage)
    case method: MethodDef => typedMethodDef(method)
    case deftree =>
      val msg = s"typed [${deftree.getClass.getName}] at node level but it is invalid"
      throw new ImplementationErrorException(msg)
  }

  def typedModuleDef(module: ModuleDef)(implicit ctx: Context.RootContext): ModuleDef = {
    module.symbol.tpe

    val interfaceCtx = Context(ctx, module.symbol)
    interfaceCtx.reAppend(module.hp.map(_.symbol) ++ module.tp.map(_.symbol): _*)

    val typedHp = module.hp.map(typedValDef(_)(interfaceCtx))
    val typedTp = module.tp.map(typedTypeDef(_)(interfaceCtx))
    module.bounds.foreach(typedBound(_)(interfaceCtx))
    val typedParents = module.parents.map(typedValDef(_)(interfaceCtx))
    val typedSiblings = module.siblings.map(typedValDef(_)(interfaceCtx))

    val componentCtx = Context(interfaceCtx)
    val typedComponents =
      module.components.map(typedDefinition(_)(componentCtx))

    val typedModule = module.copy(
      module.name,
      typedHp,
      typedTp,
      module.bounds,
      typedParents,
      typedSiblings,
      typedComponents.map(_.asInstanceOf[Component])
    )
      .setSymbol(module.symbol)
      .setID(module.id)

    TypedCache.setTree(typedModule)
    typedModule
  }

  def typedStructDef(struct: StructDef)(implicit ctx: Context): StructDef = {
    struct.symbol.tpe

    val signatureCtx = Context(ctx, struct.symbol)
    ctx.reAppend(
      struct.hp.map(_.symbol) ++
        struct.tp.map(_.symbol): _*
    )

    val typedHp = struct.hp.map(typedValDef(_)(signatureCtx))
    val typedTp = struct.tp.map(typedTypeDef(_)(signatureCtx))
    struct.bounds.foreach(typedBound(_)(signatureCtx))

    val fieldCtx = Context(signatureCtx)
    fieldCtx.reAppend(struct.fields.map(_.symbol): _*)
    val typedFields = struct.fields.map(typedValDef(_)(fieldCtx))

    val typedStruct = struct.copy(
      struct.name,
      typedHp,
      typedTp,
      struct.bounds,
      typedFields
    )
      .setSymbol(struct.symbol)
      .setID(struct.id)

    TypedCache.setTree(typedStruct)
    typedStruct
  }

  def typedImplementClass(impl: ImplementClass)(implicit ctx: Context.RootContext): ImplementClass = {
    val signatureCtx = Context(ctx, impl.symbol)

    signatureCtx.reAppend(
      impl.hp.map(_.symbol) ++
      impl.tp.map(_.symbol) :_*
    )

    val typedHp = impl.hp.map(typedValDef(_)(signatureCtx))
    val typedTp = impl.tp.map(typedTypeDef(_)(signatureCtx))
    impl.bounds.foreach(typedBound(_)(signatureCtx))

    val typedTarget = typedTypeAST(impl.target)(signatureCtx)
    typedTarget.tpe match {
      case Type.ErrorType => impl
      case targetTpe: Type.RefType =>
        val implCtx = Context(signatureCtx, targetTpe)
        implCtx.reAppend(
          impl.methods.map(_.symbol) ++
          impl.stages.map(_.symbol): _*
        )

        val typedMethods = impl.methods.map(typedMethodDef(_)(implCtx))
        val typedStages = impl.stages.map(typedStageDef(_)(implCtx))

        val typedImpl = impl.copy(
          typedTarget,
          typedHp,
          typedTp,
          impl.bounds,
          typedMethods,
          typedStages
        )
          .setSymbol(impl.symbol)
          .setID(impl.id)

        TypedCache.setTree(typedImpl)
        typedImpl
    }
  }

  def typedImplementInterface(impl: ImplementInterface)(implicit ctx: Context.RootContext): ImplementInterface = {
    val signatureCtx = Context(ctx, impl.symbol)
    signatureCtx.reAppend(
      impl.hp.map(_.symbol) ++
      impl.tp.map(_.symbol): _*
    )

    val typedHp = impl.hp.map(Typer.typedValDef(_)(signatureCtx))
    val typedTp = impl.tp.map(Typer.typedTypeDef(_)(signatureCtx))
    impl.bounds.foreach(Typer.typedBound(_)(signatureCtx))

    val typedInterface = typedTypeAST(impl.interface)(signatureCtx)
    val typedTarget = typedTypeAST(impl.target)(signatureCtx)

    typedTarget.tpe match {
      case Type.ErrorType => impl
      case targetTpe: Type.RefType =>
        val implCtx = Context(signatureCtx, targetTpe)
        implCtx.reAppend(impl.methods.map(_.symbol): _*)

        val typedMethods = impl.methods.map(Typer.typedMethodDef(_)(implCtx))

        val typedImpl = impl.copy(
          typedInterface,
          typedTarget,
          typedHp,
          typedTp,
          impl.bounds,
          typedMethods
        )
          .setSymbol(impl.symbol)
          .setID(impl.id)

        TypedCache.setTree(typedImpl)

        typedImpl
    }
  }

  def typedAlwaysDef(always: AlwaysDef)(implicit ctx: Context.NodeContext): AlwaysDef = {
    val alwaysCtx = Context(ctx, always.symbol)
    val typedBlk = typedBlock(always.blk)(alwaysCtx)

    val typedAlways = always.copy(
      always.name,
      typedBlk
    )
      .setSymbol(always.symbol)
      .setID(always.id)

    TypedCache.setTree(typedAlways)
    typedAlways
  }

  def typedMethodDef(method: MethodDef)(implicit ctx: Context.NodeContext): MethodDef = {
    method.symbol.tpe

    val signatureCtx = Context(ctx, method.symbol)
    ctx.reAppend(
      method.hp.map(_.symbol) ++
        method.tp.map(_.symbol) ++
        method.params.map(_.symbol): _*
    )

    val typedHp = method.hp.map(typedValDef(_)(signatureCtx))
    val typedTp = method.tp.map(typedTypeDef(_)(signatureCtx))
    method.bounds.foreach(typedBound(_)(signatureCtx))
    val typedParams = method.params.map(typedValDef(_)(signatureCtx))
    val typedRetTpe = typedTypeAST(method.retTpe)(signatureCtx)
    val typedBlk = method.blk.map(typedBlock(_)(signatureCtx))

    typedBlk.foreach(TypedCache.setTree)

    val typedMethod = method.copy(
      method.name,
      typedHp,
      typedTp,
      method.bounds,
      typedParams,
      typedRetTpe,
      typedBlk
    )
      .setSymbol(method.symbol)
      .setID(method.id)

    TypedCache.setTree(typedMethod)
    typedMethod
  }

  def typedValDef(vdef: ValDef)(implicit ctx: Context.NodeContext): ValDef = {
    vdef.symbol.tpe

    val typedTpeTree = vdef.tpeTree.map(typedTypeAST)
    val typedExp = vdef.expr.map(typedExpr)

    val typedValDef = vdef.copy(
      vdef.flag,
      vdef.name,
      typedTpeTree,
      typedExp
    )
      .setSymbol(vdef.symbol)
      .setID(vdef.id)

    typedExp.foreach(TypedCache.setTree)
    TypedCache.setTree(typedValDef)
    typedValDef
  }

  def typedStageDef(stage: StageDef)(implicit ctx: Context.NodeContext): StageDef = {
    stage.symbol.tpe

    val signatureCtx = Context(ctx, stage.symbol)
    ctx.reAppend(stage.params.map(_.symbol): _*)

    val typedParams = stage.params.map(typedValDef(_)(signatureCtx))
    val typedRetTpe = typedTypeAST(stage.retTpe)(signatureCtx)

    val blkCtx = Context.blk(signatureCtx)
    stage.blk.map(Namer.nodeLevelNamed(_, blkCtx))
    stage.states.map(Namer.nodeLevelNamed(_, blkCtx))

    val typedBlkElems = stage.blk.map {
      case vdef: ValDef => typedValDef(vdef)(blkCtx)
      case expr: Expression => typedExpr(expr)(blkCtx)
    }

    val typedStates = stage.states.map(typedStateDef(_)(blkCtx))

    val typedStage = stage.copy(
      stage.name,
      typedParams,
      typedRetTpe,
      typedStates,
      typedBlkElems
    )
      .setSymbol(stage.symbol)
      .setID(stage.id)

    TypedCache.setTree(typedStage)
    typedStage
  }

  def typedStateDef(state: StateDef)(implicit ctx: Context.NodeContext): StateDef = {
    val stateCtx = Context(ctx, state.symbol)
    val typedBlk = typedBlock(state.blk)(stateCtx)

    val typedState = state.copy(state.name, typedBlk)
      .setSymbol(state.symbol)
      .setID(state.id)

    TypedCache.setTree(typedState)
    typedState
  }

  def typedTypeDef(tpeDef: TypeDef)(implicit ctx: Context.NodeContext): TypeDef = {
    Namer.nodeLevelNamed(tpeDef, ctx)

    tpeDef.symbol.tpe

    val typedTpeDef = tpeDef.copy(tpeDef.name)
      .setSymbol(tpeDef.symbol)
      .setID(tpeDef.id)

    TypedCache.setTree(typedTpeDef)
    typedTpeDef
  }

  def typedBound(bound: Bound)(implicit ctx: Context.NodeContext): Unit = {
    ctx.lookup(bound.target) match {
      case Left(err) => Reporter.appendError(err)
      case Right(symbol: Symbol.TypeParamSymbol) =>
        ctx.owner match {
          case owner if symbol.owner != owner =>
            val err = Error.SetBoundForDifferentOwner(owner, symbol.owner)
            Reporter.appendError(err)
          case _ =>
            val typedTT = bound.constraints.map(typedTypeAST)
            val filteredTpe = typedTT
              .filterNot(_.tpe.isErrorType)
              .map(_.tpe.asRefType)

            symbol.setBounds(filteredTpe)
        }
      case Right(symbol) =>
        val err = Error.RequireTypeParamSymbol(symbol.name)
        Reporter.appendError(err)
    }
  }

  def typedExpr(expr: Expression)(implicit ctx: Context.NodeContext): Expression =
    expr match {
      case ident: Ident => typedExprIdent(ident)
      case select: Select => typedExprSelect(select)
      case ifExpr: IfExpr => typedIfExpr(ifExpr)
      case self: Self => typedSelf(self)
      case blk: Block => typedBlock(blk)
      case construct: Construct => ???
      case int: IntLiteral => typedIntLiteral(int)
      case string: StringLiteral => typedStringLiteral(string)
      case unit: UnitLiteral => typedUnitLiteral(unit)
      case bit: BitLiteral => typedBitLiteral(bit)
      case _: Apply =>
        throw new ImplementationErrorException("Apply tree should not be typed")
      case applyParams: ApplyParams => typedExprApplyParams(applyParams)
      case _: ApplyTypeParams =>
        throw new ImplementationErrorException(
          "ApplyTypeParam tree should be handled in typedExprApplyParams"
        )
      case generate: Generate => typedGenerate(generate)
      case goto: Goto => typedGoto(goto)
      case finish: Finish => typedFinish(finish)
      case relay: Relay => typedRelay(relay)
    }

  def typedExprIdent(ident: Ident)(implicit ctx: Context.NodeContext): Ident = {
    ctx.lookup(ident.name) match {
      case Left(err) =>
        Reporter.appendError(err)
        ident.setTpe(Type.ErrorType).setSymbol(Symbol.ErrorSymbol)
      case Right(symbol: Symbol.TypeSymbol) =>
        Reporter.appendError(Error.SymbolIsType(symbol.name))
        ident.setTpe(Type.ErrorType).setSymbol(Symbol.ErrorSymbol)
      case Right(symbol: Symbol.TermSymbol) =>
        ident.setTpe(symbol.tpe.asRefType).setSymbol(symbol)
    }
  }

  def typedExprApplyParams(apply: ApplyParams)(implicit ctx: Context.NodeContext): Apply = {
    type ResultPair = (Type.MethodType, Vector[Expression], Vector[TypeAST])

    val typedArgs = apply.args.map(typedExpr)

    def filterType(tpe: Type): Either[Error, Type.MethodType] =
      tpe match {
        case method: Type.MethodType => Right(method)
        case Type.ErrorType => Left(Error.DummyError)
        case tpe => Left(Error.RequireMethodType(tpe))
      }

    def verifyArguments(method: Type.MethodType, args: Vector[Expression]): Either[Error, Unit] = {
      val errors = verifyParamTypes(method.params, args.map(_.tpe))
      if (errors.isEmpty) Right(())
      else Left(Error.MultipleErrors(errors))
    }

    def requireTPsOrHPsMethod(applyTPs: ApplyTypeParams)(method: Type.MethodType): Either[Error, ResultPair] = {
      def rejectMethodNoTPorHP: Either[Error, Unit] = {
        val hasTP = method.typeParam.nonEmpty
        val hasHP = method.hardwareParam.nonEmpty

        if(hasTP || hasHP) Right(())
        else Left(Error.RequireTypeParameter)
      }

      def verifyTPsAndHPsLength: Either[Error, Unit] = {
        val tpLength = method.typeParam.length
        val hpLength = method.hardwareParam.length
        val expect = tpLength + hpLength
        val actual = applyTPs.hps.length + applyTPs.tps.length

        if(expect == actual) Right(())
        else Left(Error.ParameterLengthMismatch(expect, actual))
      }

      def verifyTPsAndHPs: Either[Error, (Vector[Expression], Vector[TypeAST])] ={
        val (hps, tpsFirstHalf) = applyTPs.hps.splitAt(method.hardwareParam.length)

        val typedHps = hps.map(typedExpr)
        val typedTpsFirstHalf = tpsFirstHalf.map(typedType)
        val typedTpsLatterHalf = applyTPs.tps.map(typedTypeAST)
        val typedTps = typedTpsFirstHalf ++ typedTpsLatterHalf

        val hpErrs = typedHps.filter(_.tpe.isErrorType)
        val tpErrs = typedTps.filter(_.tpe.isErrorType)
        val errs = hpErrs ++ tpErrs

        if(errs.nonEmpty) Left(Error.DummyError)
        else Right((typedHps, typedTps))
      }

      def verifyHpTypes(hps: Vector[Expression]): Either[Error, Unit] = {
        val errs = method.hardwareParam.map(_.tpe)
          .zip(hps.map(_.tpe))
          .filter{ case (a, e) => a =!= e }
          .filter{ case (a, e) => !a.isErrorType && !e.isErrorType }
          .map { case (a, e) => Error.TypeMissmatch(a, e) }

        if(errs.isEmpty) Right(())
        else Left(Error.MultipleErrors(errs))
      }

      // TODO:
      //   Replace type parameters interfaces have like below
      //     where A: Interface[B] => where A: Interface[Int]
      //
      // TODO:
      //   Implement interface implementation conflict detector
      //
      // TODO:
      //   Implement the process to deal with the case that
      //   implemented interface has type parameter and use type parameter
      //   and bound's interface use entity type like below.
      //
      //     impl[T] Interface[T] for ... where T: ... { ... }
      //
      //       and
      //
      //     def method[T](...) ... where T: Interface[u32]
      //
      //   The process need to detect Interface[T] when
      //   bounds require Interface[u32] if u32 meets T's bounds
      def verifyTpBounds(tps: Vector[TypeAST]): Either[Error, Unit] = {
        def tpChecker(boundTps: Vector[Type.RefType], interfaceTps: Vector[Type.RefType]): Boolean =
          boundTps.zip(interfaceTps).forall {
            case (boundTp, interfaceTp) => (boundTp.origin, interfaceTp.origin) match {
              case (_: Symbol.TypeParamSymbol, _: Symbol.EntityTypeSymbol) => false
              case (_: Symbol.EntityTypeSymbol, tp: Symbol.TypeParamSymbol) => verifyTpBound(boundTp, tp.getBounds).isRight
              case (_: Symbol.EntityTypeSymbol, _: Symbol.EntityTypeSymbol) => boundTp =:= interfaceTp
              case (btp: Symbol.TypeParamSymbol, itp: Symbol.TypeParamSymbol) =>
                // itp: implement interface's type parameter like below
                //
                //   impl Interface[T] for Type
                //                 ^^^
                //
                // btp: where clause's type parameter like below
                //
                //   where Interface[T]
                //                  ^^^
                // Here checks whether itp's bounds meets btp's bounds
                // So, if itp's bounds are Test0 + Test1 and btp's bounds are Test0 + Test1 + Test2,
                // it is invalid.
                // However, if itp's bounds are Test0 + Test1 and btp's bound is Test0, it is valid.
                val boundTable = itp.getBounds.groupBy(_.origin)

                btp.getBounds.forall(bb => boundTable.get(bb.origin) match {
                  case None => false
                  case Some(bounds) => bounds.exists(ib => tpChecker(bb.typeParam, ib.typeParam))
                })
            }
          }

        // verify one where clause(not all where clauses)
        def verifyTpBound(tpe: Type.RefType, bounds: Vector[Type.RefType]): Either[Error, Unit] = {
          val implss = bounds
            .map(_.origin.asInterfaceSymbol)
            .map(_.lookupImpl(tpe))

          // TODO
          //   Address the case that bound's type parameter has Self type
          val notMetBounds = bounds.zip(implss)
            .map{ case (bound, impls) => bound -> impls.map(_.targetInterface)}
            .flatMap{ case (bound, interfaces) =>
              val isMeetBound = interfaces.exists {
                interface =>
                  val isSameOrigin = bound.origin == interface.origin
                  isSameOrigin && tpChecker(bound.typeParam, interface.typeParam)
              }

              if(isMeetBound) None
              else Some(bound)
            }

          if(notMetBounds.isEmpty) Right(())
          else Left(Error.NotMeetBound(tpe, notMetBounds))
        }

        val map = (method.typeParam zip tps.map(_.tpe.asRefType)).toMap
        val bounds = method.typeParam
          .map(_.asTypeParamSymbol)
          .map(_.getBounds)
          .map(_.map(_.replaceWithTypeParamMap(map)))

        val errors = tps.map(_.tpe).zip(bounds).map{
          case (tpe: Type.RefType, bound) => verifyTpBound(tpe, bound)
          case (Type.ErrorType, _) => ???
        }.collect { case Left(err) => err }

        if(errors.isEmpty) Right(())
        else Left(Error.MultipleErrors(errors))
      }

      for {
        _ <- rejectMethodNoTPorHP
        _ <- verifyTPsAndHPsLength
        pairs <- verifyTPsAndHPs
        (hps, tps) = pairs
        _ <- verifyHpTypes(hps)
        _ <- verifyTpBounds(tps)
        map = method.typeParam.zip(tps.map(_.tpe.asRefType)).toMap
        methodTpe = method.replaceWithTypeParamMap(map)
      } yield (methodTpe, hps, tps)
    }

    def rejectTPsOrHPsMethod(method: Type.MethodType): Either[Error, ResultPair] = {
      val hasHP = method.hardwareParam.nonEmpty
      val hasTP = method.typeParam.nonEmpty

      if(hasHP || hasTP) Left(Error.NoNeedTypeParameter(method))
      else Right((method, Vector.empty, Vector.empty))
    }

    def succeed(symbol: Symbol)(requireTPs: Type.MethodType => Either[Error, ResultPair]): Either[Error, ResultPair] = {
      for {
        methodTpe0 <- filterType(symbol.tpe)
        pairs <- requireTPs(methodTpe0)
        (methodTpe1, hps, tps) = pairs
        _ <- verifyArguments(methodTpe1, typedArgs)
      } yield (methodTpe1, hps, tps)
    }

    def lookupSelectSymbol(select: Select)(
      requireTP: Type.MethodType => Either[Error, ResultPair],
      errorApplyGen: Expression => Apply,
      succeedApplyGen: (Expression, Vector[Expression], Vector[TypeAST], Type.RefType) => Apply
    ): Apply = {
      def downcastToRefType(tpe: Type): Either[Error, Type.RefType] =
        tpe match {
          case refTpe: Type.RefType => Right(refTpe)
          case _ => Left(Error.DummyError)
        }

      def lookup(tpe: Type.RefType): Either[Error, Symbol] =
        tpe.lookupMethod(select.name) match {
          case LookupResult.LookupSuccess(symbol) => Right(symbol)
          case LookupResult.LookupFailure(err) => Left(err)
        }

      val typedSuffix = typedExpr(select.expr)
      val result = for {
        refTpe <- downcastToRefType(typedSuffix.tpe)
        symbol <- lookup(refTpe)
        pair <- succeed(symbol)(requireTP)
      } yield pair


      val selectTpe = result match {
        case Left(_) => Type.ErrorType
        case Right((methodTpe, _, _)) => methodTpe
      }

      val typedSelect = Select(typedSuffix, select.name).setTpe(selectTpe)

      result match {
        case Left(err) =>
          Reporter.appendError(err)
          errorApplyGen(typedSelect)
        case Right((method, hps, tps)) =>
          succeedApplyGen(typedSelect, hps, tps, method.returnType)
      }
    }

    def lookupExprSymbol(expr: Expression)(
      requireTP: Type.MethodType => Either[Error, ResultPair],
      errorApply: Expression => Apply,
      succeedApplyGen: (Expression, Vector[Expression], Vector[TypeAST], Type.RefType) => Apply
    ): Apply = {
      val typedExp = typedExpr(expr)

      val result = for {
        methodTpe0 <- filterType(typedExp.tpe)
        methodTpe1 <- requireTP(methodTpe0)
      } yield methodTpe1

      result match {
        case Left(err) =>
          Reporter.appendError(err)
          errorApply(typedExp)
        case Right((methodTpe, hps, tps)) =>
          succeedApplyGen(typedExp, hps, tps, methodTpe.returnType)
      }
    }

    def errorApplyWithTPsOrHPs(hps: Vector[Expression])(expr: Expression): Apply =
      Apply(expr, hps, Vector.empty, typedArgs).setTpe(Type.ErrorType).setID(apply.id)

    def succeedApplyWithTPsOrHPs(expr: Expression, hps: Vector[Expression], tps: Vector[TypeAST], tpe: Type.RefType): Apply =
      Apply(expr, hps, tps, typedArgs).setTpe(tpe).setID(apply.id)

    def errorApplyWithoutTPsOrHPs(expr: Expression): Apply =
      Apply(expr, Vector.empty, Vector.empty, typedArgs).setTpe(Type.ErrorType).setID(apply.id)

    def succeedApplyWithoutTPsOrHPs(expr: Expression, _hps: Vector[Expression], _tps: Vector[TypeAST], tpe: Type.RefType): Apply =
      Apply(expr, Vector.empty, Vector.empty, typedArgs).setTpe(tpe).setID(apply.id)

    apply.suffix match {
      case applyTPs @ ApplyTypeParams(select: Select, _, _) =>
        lookupSelectSymbol(select)(
          requireTPsOrHPsMethod(applyTPs),
          errorApplyWithTPsOrHPs(applyTPs.hps),
          succeedApplyWithTPsOrHPs
        )
      case applyTPs: ApplyTypeParams =>
        lookupExprSymbol(applyTPs.suffix)(
          requireTPsOrHPsMethod(applyTPs),
          errorApplyWithTPsOrHPs(applyTPs.hps),
          succeedApplyWithTPsOrHPs
        )
      case select: Select =>
        lookupSelectSymbol(select)(
          rejectTPsOrHPsMethod,
          errorApplyWithoutTPsOrHPs,
          succeedApplyWithoutTPsOrHPs
        )
      case expr: Expression =>
        lookupExprSymbol(expr)(
          rejectTPsOrHPsMethod,
          errorApplyWithoutTPsOrHPs,
          succeedApplyWithoutTPsOrHPs
        )
    }
  }

  def typedExprSelect(select: Select)(implicit ctx: Context.NodeContext): Select = {
    val typedSuffix = typedExpr(select.expr)
    typedSuffix.tpe match {
      case refTpe: Type.RefType =>
        // This method only for reference to field of struct or module.
        // That's why this method does not look up method.
        refTpe.lookupField(select.name) match {
          case LookupResult.LookupFailure(err) =>
            Reporter.appendError(err)
            select.copy(typedSuffix, select.name)
              .setTpe(Type.ErrorType)
              .setSymbol(Symbol.ErrorSymbol)
              .setID(select.id)
          case LookupResult.LookupSuccess(symbol) =>
            val map = {
              val refTpe = typedSuffix.tpe.asRefType

              refTpe.origin.tpe match {
                case _: Type.ParameterType => Map.empty[Symbol.TypeParamSymbol, Type.RefType]
                case tpe: Type.EntityType =>
                  tpe.typeParam
                    .zip(refTpe.typeParam)
                    .map { case (sym, tpe) => sym -> tpe }
                    .toMap
              }
            }

            val selectTpe = symbol.tpe match {
              case tpe: Type.RefType =>
                tpe.replaceWithTypeParamMap(map)
              case tpe: Type.MethodType =>
                tpe.replaceWithTypeParamMap(map)
              case Type.ErrorType =>
                Type.ErrorType
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

  def typedBlock(blk: Block)(implicit ctx: Context.NodeContext): Block = {
    val blkCtx = Context.blk(ctx)

    val typedElems = blk.elems.map {
      case vdef: ValDef => typedValDef(vdef)(blkCtx)
      case expr: Expression => typedExpr(expr)(blkCtx)
    }

    val typedLast = typedExpr(blk.last)(blkCtx)

    Block(typedElems, typedLast).setTpe(typedLast.tpe).setID(blk.id)
  }

  def typedSelf(self: Self)(implicit ctx: Context.NodeContext): Self = {
    ctx.self match {
      case None =>
        Reporter.appendError(Error.UsingSelfOutsideClass)
        Self().setTpe(Type.ErrorType).setID(self.id)
      case Some(tpe) =>
        Self().setTpe(tpe).setID(self.id)
    }
  }

  def typedIfExpr(ifexpr: IfExpr)(implicit ctx: Context.NodeContext): IfExpr = {
    val typedCond = typedExpr(ifexpr.cond)
    val typedConseq = typedExpr(ifexpr.conseq)
    val typedAlt = ifexpr.alt.map(typedExpr)

    def isBoolTpe = typedCond.tpe != Type.boolTpe
    def isBit1Tpe = typedCond.tpe != Type.bitTpe(IntLiteral(1))
    def isErrorTpe = typedCond.tpe.isErrorType
    if (!isBoolTpe && !isBit1Tpe && !isErrorTpe)
      Reporter.appendError(Error.RequireBooleanType(typedCond.tpe))

    typedAlt match {
      case None =>
        IfExpr(typedCond, typedConseq, typedAlt).setTpe(Type.unitTpe).setID(ifexpr.id)
      case Some(alt) =>
        val retTpe = (alt.tpe, typedConseq.tpe) match {
          case (Type.ErrorType, tpe) => tpe
          case (tpe, Type.ErrorType) => tpe
          case (altTpe, conseqTpe)  =>
            if(altTpe =!= conseqTpe)
              Reporter.appendError(Error.TypeMissmatch(altTpe, conseqTpe))

            altTpe
        }

        IfExpr(typedCond, typedConseq, typedAlt).setTpe(retTpe).setID(ifexpr.id)
    }
  }

  def typedType(expr: Expression)(implicit ctx: Context.NodeContext): TypeTree =
    expr match {
      case ident: Ident => typedTypeIdent(ident)
      case apply: ApplyTypeParams => typedTypeApplyTypeParams(apply)
      case expr =>
        Reporter.appendError(Error.InvalidFormatForType(expr))
        TypeTree("", Vector.empty, Vector.empty).setTpe(Type.ErrorType)
    }

  def typedTypeIdent(ident: Ident)(implicit ctx: Context.NodeContext): TypeTree = {
    val tt = ctx.lookup(ident.name) match {
      case Left(err) =>
        Reporter.appendError(err)
        TypeTree(ident.name, Vector.empty, Vector.empty).setTpe(Type.ErrorType)
      case Right(symbol: Symbol.TermSymbol) =>
        Reporter.appendError(Error.SymbolIsTerm(symbol.name))
        TypeTree(symbol.name, Vector.empty, Vector.empty).setTpe(Type.ErrorType)
      case Right(symbol: Symbol.TypeSymbol) =>
        /*
         * If a type requires type parameter, this process cause error
         * because this process expect only monomorphic type
         * like Int and String, and not List[_] and Option[_].
         */
        val retTpe = symbol.tpe match {
          case tpe: Type.EntityType if tpe.hardwareParam.nonEmpty || tpe.typeParam.nonEmpty =>
            Reporter.appendError(Error.RequireTypeParameter)
            Type.ErrorType
          case _ =>
            Type.RefType(symbol, Vector.empty, Vector.empty)
        }

        TypeTree(symbol.name, Vector.empty, Vector.empty).setTpe(retTpe)
    }

    tt.setID(ident.id)
  }

  def typedTypeApplyTypeParams(apply: ApplyTypeParams)(implicit ctx: Context.NodeContext): TypeTree = {
    val ApplyTypeParams(Ident(name), hps, tps) = apply

    val tt = ctx.lookup(name) match {
      case Left(err) =>
        Reporter.appendError(err)
        TypeTree(name, Vector.empty, Vector.empty).setTpe(Type.ErrorType)
      case Right(symbol: Symbol.TermSymbol) =>
        Reporter.appendError(Error.SymbolIsTerm(symbol.name))
        TypeTree(name, Vector.empty, Vector.empty).setTpe(Type.ErrorType)
      case Right(symbol: Symbol.TypeSymbol) =>
        symbol.tpe match {
          /**
           * For now, there is no plan to support higher-kind type.
           * So, this pattern match rejects [[Type.ParameterType]]
           */
          case _: Type.ParameterType =>
            Reporter.appendError(Error.RejectHigherKind)
            TypeTree(symbol.name, apply.hps, apply.tps).setTpe(Type.ErrorType)
          case tpe: Type.EntityType => verifyTypeParams(symbol, hps, tps, tpe)
        }
    }

    tt.setID(apply.id)
  }

  def typedTypeAST(typeAST: TypeAST)(implicit ctx: Context.NodeContext): TypeAST = {
    val tpeAST = typeAST match {
      case typeTree: TypeTree => typedTypeTree(typeTree)
      case self: SelfType => typedSelfType(self)
      case select: SelectType => typedSelectType(select)
    }

    tpeAST.setID(typeAST.id)
  }

  def typedTypeTree(typeTree: TypeTree)(implicit ctx: Context.NodeContext): TypeTree =
    ctx.lookup(typeTree.name) match {
      case Left(err) =>
        Reporter.appendError(err)
        typeTree.setTpe(Type.ErrorType)
      case Right(symbol: Symbol.TermSymbol) =>
        Reporter.appendError(Error.SymbolIsTerm(symbol.name))
        typeTree.setTpe(Type.ErrorType)
      case Right(symbol: Symbol.TypeSymbol) =>
        symbol.tpe match {
          case tpe: Type.EntityType => verifyTypeParams(symbol, typeTree.hp, typeTree.tp, tpe)
          case tpe: Type.ParameterType =>
            /**
             * For now, there is no plan to support higher-kind type.
             * So, ParameterType with tyep parameters like T[A] is rejected
             */
            val treeTpe =
              if(typeTree.hp.isEmpty && typeTree.tp.isEmpty) tpe
              else {
                Reporter.appendError(Error.RejectHigherKind)
                Type.ErrorType
              }

            typeTree.setTpe(treeTpe)
        }

    }

  def typedSelfType(self: SelfType)(implicit ctx: Context.NodeContext): SelfType =
    ctx.self match {
      case None =>
        Reporter.appendError(Error.UsingSelfOutsideClass)
        self.setTpe(Type.ErrorType)
      case Some(tpe) =>
        self.setTpe(tpe)
    }

  def typedSelectType(select: SelectType)(implicit ctx: Context.NodeContext): SelectType = {
    val typedSuffix = select.suffix match {
      case suffix: SelectType => typedSelectType(suffix)
      case suffix: TypeTree => typedTypeTree(suffix)
      case suffix: SelfType => typedSelfType(suffix)
    }

    val selectTpe = typedSuffix.tpe match {
      case Type.ErrorType => Type.ErrorType
      case tpe: Type.RefType => tpe.lookupType(select.name) match {
        case Right(t) => t
        case Left(err) =>
          Reporter.appendError(err)
          Type.ErrorType
      }
    }

    SelectType(typedSuffix, select.name).setTpe(selectTpe).setID(select.id)
  }

  def typedBitLiteral(bit: BitLiteral)(implicit ctx: Context.NodeContext): BitLiteral = {
    val bitSymbol = Symbol.lookupBuiltin("Bit")
    val intSymbol = Symbol.lookupBuiltin("Int")
    val intTpe = Type.RefType(intSymbol, Vector.empty, Vector.empty)
    val length = IntLiteral(bit.length).setTpe(intTpe)

    val bitTpe = Type.RefType(bitSymbol, Vector(length), Vector.empty)

    bit.setTpe(bitTpe).setID(bit.id)
  }

  def typedIntLiteral(int: IntLiteral)(implicit ctx: Context.NodeContext): IntLiteral = {
    val intSymbol = Symbol.lookupBuiltin("Int")
    val intTpe = Type.RefType(intSymbol)

    int.setTpe(intTpe).setID(int.id)
  }

  def typedUnitLiteral(unit: UnitLiteral)(implicit ctx: Context.NodeContext): UnitLiteral = {
    val unitSymbol = Symbol.lookupBuiltin("Unit")
    val unitTpe = Type.RefType(unitSymbol)

    unit.setTpe(unitTpe).setID(unit.id)
  }

  def typedStringLiteral(str: StringLiteral)(implicit ctx: Context.NodeContext): StringLiteral = {
    val strSymbol = Symbol.lookupBuiltin("String")
    val strTpe = Type.RefType(strSymbol)

    str.setTpe(strTpe).setID(str.id)
  }

  def typedFinish(finish: Finish)(implicit ctx: Context.NodeContext): Finish = {
    ctx.owner match {
      case _: Symbol.StateSymbol =>
      case _: Symbol.StageSymbol =>
      case _ =>
        Reporter.appendError(Error.FinishOutsideStage)
    }

    finish.setTpe(Type.unitTpe).setID(finish.id)
  }

  def typedGoto(goto: Goto)(implicit ctx: Context.NodeContext): Goto = {
    ctx.owner match {
      case _: Symbol.StateSymbol =>
        ctx.lookup(goto.target) match {
          case Left(err) => Reporter.appendError(err)
          case Right(_: Symbol.StateSymbol) =>
          case Right(symbol) =>
            Reporter.appendError(Error.RequireStateSymbol(symbol.name))
        }
      case _ =>
        Reporter.appendError(Error.GotoOutsideState)
    }

    goto.setTpe(Type.unitTpe).setID(goto.id)
  }

  def typedGenerate(generate: Generate)(implicit ctx: Context.NodeContext): Generate = {
    val tpe = ctx.lookup(generate.target) match {
      case Left(err) =>
        Reporter.appendError(err)
        Type.ErrorType
      case Right(symbol: Symbol.StageSymbol) =>
        val tpe = symbol.tpe.asMethodType
        val typedArgs = generate.params.map(typedExpr)

        verifyParamTypes(tpe.params, typedArgs.map(_.tpe)).foreach(Reporter.appendError)
        tpe.returnType
      case Right(symbol) =>
        Reporter.appendError(Error.RequireStageSymbol(symbol.name))
        Type.ErrorType
    }

    generate.setTpe(tpe)
  }

  def typedRelay(relay: Relay)(implicit ctx: Context.NodeContext): Relay = {
    ctx.owner match {
      case _: Symbol.StageSymbol =>
      case _: Symbol.StateSymbol =>
      case _ => Reporter.appendError(Error.RelayOutsideStage)
    }

    val tpe = ctx.lookup(relay.target) match {
      case Left(err) =>
        Reporter.appendError(err)
        Type.ErrorType
      case Right(symbol: Symbol.StageSymbol) =>
        val tpe = symbol.tpe.asMethodType
        val typedArgs = relay.params.map(typedExpr)

        verifyParamTypes(tpe.params, typedArgs.map(_.tpe)).foreach(Reporter.appendError)

        tpe.returnType
      case Right(symbol) =>
        Reporter.appendError(Error.RequireStageSymbol(symbol.name))
        Type.ErrorType
    }

    relay.setTpe(tpe)
  }

  def verifyParamTypes(expect: Vector[Type], actual: Vector[Type])(implicit ctx: Context.NodeContext): Vector[Error] = {
    if (expect.length != actual.length)
      return Vector(Error.ParameterLengthMismatch(expect.length, actual.length))

    (expect zip actual)
      .filter { case (e, a) => e =!= a }
      .map { case (e, a) => Error.TypeMissmatch(e, a) }
  }

  def verifyParamType(expect: Type, actual: Type)(implicit ctx: Context.NodeContext): Vector[Error] =
    verifyParamTypes(Vector(expect), Vector(actual))

  def verifyTypeParams(
    symbol: Symbol.TypeSymbol,
    hps: Vector[Expression],
    tps: Vector[TypeAST],
    tpe: Type.EntityType
  )(
    implicit ctx: Context.NodeContext
  ): TypeTree = {
    val actualLength = hps.length + tps.length
    val expectLength = tpe.hardwareParam.length + tpe.typeParam.length

    if (expectLength != actualLength) {
      Reporter.appendError(Error.ParameterLengthMismatch(expectLength, actualLength))

      return TypeTree(symbol.name, hps, tps).setTpe(Type.ErrorType)
    }

    val (splitHps, tpsFrontHalf) = hps.splitAt(tpe.hardwareParam.length)

    val typedHps = splitHps.map(typedExpr)
    val typedTpsFrontHalf = tpsFrontHalf.map(typedType)
    val typedTpsLatterHalf = tps.map(typedTypeAST)
    val typedTps = typedTpsFrontHalf ++ typedTpsLatterHalf

    val treeTpe =
      if (typedHps.exists(_.tpe.isErrorType) || typedTps.exists(_.tpe.isErrorType))
        Type.ErrorType
      else
        Type.RefType(symbol, typedHps, typedTps.map(_.tpe.asRefType))

    TypeTree(symbol.name, typedHps, typedTps).setTpe(treeTpe)
  }
}

object TypedCache {
  import scala.collection.mutable

  private val cache = mutable.Map[Int, AST]()

  def setTree(tree: AST): Unit = {
    cache(tree.id) = tree
  }

  def getTree(tree: AST): Option[AST] = cache.get(tree.id)
}
