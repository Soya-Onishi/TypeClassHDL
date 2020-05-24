package tchdl.typecheck

import tchdl.ast._
import tchdl.util.TchdlException.ImplementationErrorException
import tchdl.util.{Context, Error, LookupResult, Reporter, Symbol, Type, Modifier}

import scala.reflect.ClassTag
import scala.reflect.runtime.universe.TypeTag

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

    val typedTarget = typedTypeTree(impl.target)(signatureCtx, acceptPkg = false)
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

    val typedInterface = typedTypeTree(impl.interface)(signatureCtx, acceptPkg = false)
    val typedTarget = typedTypeTree(impl.target)(signatureCtx, acceptPkg = false)

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
    val typedParams = method.params.map(typedValDef(_)(signatureCtx))
    val typedRetTpe = typedTypeTree(method.retTpe)(signatureCtx, acceptPkg = false)
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

    val typedTpeTree = vdef.tpeTree.map(typedTypeTree(_)(ctx, acceptPkg = false))
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
    val typedRetTpe = typedTypeTree(stage.retTpe)(signatureCtx, acceptPkg = false)

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

  def typedExpr(expr: Expression)(implicit ctx: Context.NodeContext): Expression =
    expr match {
      case ident: Ident => typedExprIdent(ident)
      case select: Select => typedExprSelect(select)
      case binop: BinOp => typedBinOp(binop)
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
      case select: StaticSelect => throw new ImplementationErrorException("StaticSelect must not appear here")
    }

  def typedExprIdent(ident: Ident)(implicit ctx: Context.NodeContext): Ident = {
    ctx.lookup[Symbol.TermSymbol](ident.name) match {
      case LookupResult.LookupFailure(err) =>
        Reporter.appendError(err)
        ident.setTpe(Type.ErrorType).setSymbol(Symbol.ErrorSymbol)
      case LookupResult.LookupSuccess(symbol) =>
        ident.setTpe(symbol.tpe.asRefType).setSymbol(symbol)
    }
  }

  def typedExprApplyParams(apply: ApplyParams)(implicit ctx: Context.NodeContext): Apply = {
    type ResultPair = (Type.MethodType, Vector[Expression], Vector[TypeTree])

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

      def verifyTPsAndHPs: Either[Error, (Vector[Expression], Vector[TypeTree])] ={
        val (hps, tpsFirstHalf) = applyTPs.hps.splitAt(method.hardwareParam.length)

        val typedHps = hps.map(typedExpr)
        val typedTpsFirstHalf = tpsFirstHalf.map(typedType)
        val typedTpsLatterHalf = applyTPs.tps.map(typedTypeTree(_)(ctx, acceptPkg = false))
        val typedTps = typedTpsFirstHalf ++ typedTpsLatterHalf

        val hasErrInHardArg = typedHps.exists(_.tpe.isErrorType)
        val hardArgErrs = typedHps.zip(method.hardwareParam)
          .filterNot{ case (harg, hparam) => harg.tpe.isErrorType || hparam.tpe.isErrorType }
          .filterNot { case (harg, hparam) => harg.tpe =:= hparam.tpe }
          .map { case (harg, hparam) => Error.TypeMissmatch(hparam.tpe, harg.tpe) }

        val hasErrInTypeArg = typedTps.exists(_.tpe.isErrorType)
        val typeArgErrs = typedTps.zip(method.typeParam)
          .filterNot{ case (targ, _) => targ.tpe.isErrorType }
          .filterNot{ case (targ, tparam) => targ.tpe.asRefType <|= Type.RefType(tparam) }
          .map { case (targ, tparam) => Error.NotMeetBound(targ.tpe, tparam.getBounds) }

        (hardArgErrs ++ typeArgErrs).foreach(Reporter.appendError)

        val isInvalid = hasErrInHardArg || hardArgErrs.nonEmpty || hasErrInTypeArg || typeArgErrs.nonEmpty
        if(isInvalid) Left(Error.DummyError)
        else Right((typedHps, typedTps))
      }

      /*
      // TO_DO:
      //   Replace type parameters interfaces have like below
      //     where A: Interface[B] => where A: Interface[Int]
      //
      // TO_DO:
      //   Implement interface implementation conflict detector
      //
      // TO_DO:
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
      */
      /*
      def verifyTpBounds(tps: Vector[TypeTree]): Either[Error, Unit] = {
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

        val map = (method.typeParam.map(_.asTypeParamSymbol) zip tps.map(_.tpe.asRefType)).toMap
        val bounds = method.typeParam
          .map(_.asTypeParamSymbol)
          .map(_.getBounds)
          .map(_.map(_.replaceWithTypeParamMap(map)))

        val errors = tps.map(_.tpe).zip(bounds).map{
          case (tpe: Type.RefType, bound) => verifyTpBound(tpe, bound)
          case (Type.ErrorType, _) => ???
          case (tpe, _) => throw new ImplementationError
        }.collect { case Left(err) => err }

        if(errors.isEmpty) Right(())
        else Left(Error.MultipleErrors(errors))
      }
      */

      for {
        _ <- rejectMethodNoTPorHP
        _ <- verifyTPsAndHPsLength
        pairs <- verifyTPsAndHPs
        (hps, tps) = pairs
        map = (method.typeParam.map(_.asTypeParamSymbol) zip tps.map(_.tpe.asRefType)).toMap
        methodTpe = method.replaceWithMap(map)
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
      succeedApplyGen: (Expression, Vector[Expression], Vector[TypeTree], Type.RefType) => Apply
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
      succeedApplyGen: (Expression, Vector[Expression], Vector[TypeTree], Type.RefType) => Apply
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

    def succeedApplyWithTPsOrHPs(expr: Expression, hps: Vector[Expression], tps: Vector[TypeTree], tpe: Type.RefType): Apply =
      Apply(expr, hps, tps, typedArgs).setTpe(tpe).setID(apply.id)

    def errorApplyWithoutTPsOrHPs(expr: Expression): Apply =
      Apply(expr, Vector.empty, Vector.empty, typedArgs).setTpe(Type.ErrorType).setID(apply.id)

    def succeedApplyWithoutTPsOrHPs(expr: Expression, _hps: Vector[Expression], _tps: Vector[TypeTree], tpe: Type.RefType): Apply =
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
                tpe.replaceWithMap(map)
              case tpe: Type.MethodType =>
                tpe.replaceWithMap(map)
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

  def typedBinOp(binop: BinOp)(implicit ctx: Context.NodeContext): Apply = {
    def resolveOperator(leftTpe: Type.RefType, rightTpe: Type.RefType): (Type, Symbol) = {
      val pkg = Vector("std", "ops")
      val opsPkg = Symbol.RootPackageSymbol.search(pkg).toOption.get
      val interface = opsPkg.lookup[Symbol.InterfaceSymbol](binop.op.toInterface).toOption.get
      val impls = interface.lookupImpl(leftTpe)
      val methods = for {
        impl <- impls
        method <- impl.lookup[Symbol.MethodSymbol](binop.op.toMethod)
        methodTpe = method.tpe.asMethodType
        if !methodTpe.params.exists(_.isErrorType)
        if rightTpe <|= methodTpe.params.head.asRefType
      } yield method

      methods match {
        case Vector() => Reporter.appendError(Error.SymbolNotFound(binop.op.toOperator)); (Type.ErrorType, Symbol.ErrorSymbol)
        case methods => Reporter.appendError(Error.AmbiguousSymbols(methods)); (Type.ErrorType, Symbol.ErrorSymbol)
        case Vector(method) => (method.tpe, method)
      }
    }

    val typedLeft = typedExpr(binop.left)
    val typedRight = typedExpr(binop.right)

    val (methodTpe, methodSymbol) = (typedLeft.tpe, typedRight.tpe) match {
      case (Type.ErrorType, _) => Type.ErrorType
      case (_, Type.ErrorType) => Type.ErrorType
      case (leftTpe: Type.RefType, rightTpe: Type.RefType) => resolveOperator(leftTpe, rightTpe)
    }

    val retTpe = methodTpe match {
      case tpe: Type.MethodType => tpe.returnType
      case Type.ErrorType => Type.ErrorType
    }

    Apply(
      Select(typedLeft, binop.op.toMethod).setTpe(methodTpe).setSymbol(methodSymbol),
      Vector.empty,
      Vector.empty,
      Vector(typedRight)
    )
      .setTpe(retTpe)
      .setID(binop.id)
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

  def typedType(expr: Expression)(implicit ctx: Context.NodeContext): TypeTree = {
    def typedTypeIdentFromExpr(ident: Ident): TypeTree = {
      ctx.lookup[Symbol.TypeSymbol](ident.name) match {
        case LookupResult.LookupFailure(err) =>
          Reporter.appendError(err)
          TypeTree(ident, Vector.empty, Vector.empty)
            .setTpe(Type.ErrorType)
            .setSymbol(Symbol.ErrorSymbol)
            .setID(ident.id)
        case LookupResult.LookupSuccess(symbol: Symbol.EntityTypeSymbol) =>
          verifyTypeParams(symbol, Vector.empty, Vector.empty, symbol.tpe.asEntityType)
        case LookupResult.LookupSuccess(symbol: Symbol.TypeParamSymbol) =>
          TypeTree(ident, Vector.empty, Vector.empty)
            .setTpe(Type.RefType(symbol, Vector.empty, Vector.empty))
            .setSymbol(symbol)
            .setID(ident.id)
      }
    }

    /**
     * This method is called at only first time.
     *
     * I.E.
     *    if the code is `A::B::C`, this method is called only for (1).
     *    And also, (2) is typed at [[typedSelectType]]
     *    StaticSelect(                                           |
     *      TypeTree(                                             |
     *        StaticSelect(TypeTree(Ident(A), _, _), B) |---(2)   |
     *        _, _,                                               |---(1)
     *      )                                                     |
     *      C                                                     |
     *    )                                                       |
     *
     * That's why this method return TypeTree
     * instead of StaticSelect which [[typedSelectType]] returns.
     *
     * This method also is called only from [[typedType]].
     * For now, a type tree of Expression form is only for type parameter's expression part,
     * and if parser detect `type with type parameter` or `self type`,
     * parser transitions to type part.
     * So, this method expect type without type parameter, and
     * if a looked up type require type parameters,
     * it is treated as invalid and returned as erroneous type tree.
     */
    def typedTypeStaticSelectFromExpr(select: StaticSelect): TypeTree = {
      val typedTT = typedTypeTree(select.suffix)(ctx, acceptPkg = true)

      def errorTypeTree =
        TypeTree(StaticSelect(typedTT, select.name), Vector.empty, Vector.empty)
          .setTpe(Type.ErrorType)
          .setSymbol(Symbol.ErrorSymbol)
          .setID(select.id)

      def postProcessForLookup(result: LookupResult[Symbol.TypeSymbol]): TypeTree = result match {
        case LookupResult.LookupFailure(err) =>
          Reporter.appendError(err)
          errorTypeTree
        case LookupResult.LookupSuccess(symbol) =>
          verifyTypeParams(symbol, Vector.empty, Vector.empty, symbol.tpe.asEntityType)
      }

      typedTT.symbol match {
        case ps: Symbol.PackageSymbol => postProcessForLookup(ps.lookup[Symbol.TypeSymbol](select.name))
        case _: Symbol.TypeSymbol => postProcessForLookup(typedTT.tpe.asRefType.lookupType(select.name))
        case Symbol.ErrorSymbol => errorTypeTree
        case symbol =>
          val msg = s"${symbol.getClass} should not appear here"
          throw new ImplementationErrorException(msg)
      }
    }

    expr match {
      case ident: Ident => typedTypeIdentFromExpr(ident)
      case select: StaticSelect => typedTypeStaticSelectFromExpr(select)
      case expr =>
        Reporter.appendError(Error.InvalidFormatForType(expr))
        TypeTree(Ident(""), Vector.empty, Vector.empty)
          .setTpe(Type.ErrorType)
          .setSymbol(Symbol.ErrorSymbol)
          .setID(expr.id)
    }
  }

  def typedTypeAST(typeAST: TypeAST)(implicit ctx: Context.NodeContext, acceptPkg: Boolean): TypeAST = {
    val tpeAST = typeAST match {
      case ident: Ident => typedTypeIdent(ident)
      case self: SelfType => typedSelfType(self)
      case select: StaticSelect => typedSelectType(select)
    }

    tpeAST.setID(typeAST.id)
  }

  def typedTypeTree(typeTree: TypeTree)(implicit ctx: Context.NodeContext, acceptPkg: Boolean): TypeTree = {
    def errorTpe(suffix: TypeAST) = TypeTree(suffix, typeTree.hp, typeTree.tp)
      .setTpe(Type.ErrorType)
      .setSymbol(Symbol.ErrorSymbol)
      .setID(typeTree.id)

    def buildTypeTree(suffix: TypeAST): Either[Error, TypeTree] = {
      suffix.symbol match {
        case Symbol.ErrorSymbol =>
          Right(typeTree.setSymbol(Symbol.ErrorSymbol).setTpe(Type.ErrorType))
        /**
         * There is no need to verify whether acceptPkg is true or false
         * because that check is already done in [[typedSelectType]] or [[typedTypeIdent]].
         */
        case packageSymbol: Symbol.PackageSymbol =>
          if(typeTree.hp.nonEmpty || typeTree.tp.nonEmpty) Left(Error.RejectTypeParam[Symbol.PackageSymbol]())
          else Right(
            TypeTree(suffix, Vector.empty, Vector.empty)
              .setSymbol(packageSymbol)
              .setTpe(Type.NoType)
              .setID(typeTree.id)
          )
        case typeSymbol: Symbol.TypeParamSymbol =>
          if(typeTree.hp.nonEmpty || typeTree.tp.nonEmpty) Left(Error.RejectTypeParam[Symbol.TypeParamSymbol]())
          else Right(
            TypeTree(suffix, Vector.empty, Vector.empty)
              .setSymbol(typeSymbol)
              .setTpe(typeSymbol.tpe)
              .setID(typeTree.id)
          )
        case typeSymbol: Symbol.EntityTypeSymbol =>
          Right(verifyTypeParams(typeSymbol, typeTree.hp, typeTree.tp, typeSymbol.tpe.asEntityType))
        case symbol =>
          val msg = s"${symbol.getClass} should not appear here"
          throw new ImplementationErrorException(msg)
      }
    }

    val suffix = typedTypeAST(typeTree.expr)
    val tt = suffix match {
      case ident: Ident => buildTypeTree(ident)
      case select: StaticSelect => buildTypeTree(select)
      case self: SelfType => self.tpe match {
        case _: Type.RefType =>
          if(typeTree.hp.nonEmpty || typeTree.tp.nonEmpty) Left(Error.RejectTPFromSelf)
          else Right(
            TypeTree(self, Vector.empty, Vector.empty)
              .setTpe(self.tpe)
              .setSymbol(self.symbol)
              .setID(typeTree.id)
          )
        case Type.ErrorType => Right(errorTpe(self))
      }
    }

    tt match {
      case Right(tt) => tt
      case Left(err) =>
        Reporter.appendError(err)
        TypeTree(suffix, typeTree.hp, typeTree.tp)
          .setTpe(Type.ErrorType)
          .setSymbol(Symbol.ErrorSymbol)
          .setID(typeTree.id)
    }
  }

  def typedTypeIdent(ident: Ident)(implicit ctx: Context.NodeContext, acceptPkg: Boolean): Ident = {
    val symbol = ctx.lookup[Symbol](ident.name) match {
      case LookupResult.LookupSuccess(symbol: Symbol.TypeSymbol) => symbol
      case LookupResult.LookupSuccess(symbol: Symbol.PackageSymbol) if acceptPkg => symbol
      case LookupResult.LookupSuccess(symbol) =>
        Reporter.appendError(Error.RequireSymbol[Symbol.TypeSymbol](symbol))
        Symbol.ErrorSymbol
      case LookupResult.LookupFailure(err) =>
        Reporter.appendError(err)
        Symbol.ErrorSymbol

    }

    ident.setSymbol(symbol).setTpe(Type.NoType)
  }


  def typedSelfType(self: SelfType)(implicit ctx: Context.NodeContext): SelfType =
    ctx.self match {
      case None =>
        Reporter.appendError(Error.UsingSelfOutsideClass)
        self.setTpe(Type.ErrorType).setSymbol(Symbol.ErrorSymbol)
      case Some(tpe) =>
        self.setTpe(tpe).setSymbol(tpe.origin)
    }

  def typedSelectType(select: StaticSelect)(implicit ctx: Context.NodeContext, acceptPkg: Boolean): StaticSelect = {
    val typedSuffix = typedTypeTree(select.suffix)(ctx, acceptPkg = true)
    def errorPair = (Symbol.ErrorSymbol, Type.ErrorType)

    val (symbol, tpe) = typedSuffix.symbol match {
      case Symbol.ErrorSymbol => errorPair
      case packageSymbol: Symbol.PackageSymbol =>
        packageSymbol.lookup(select.name) match {
          case LookupResult.LookupSuccess(symbol) => (symbol, Type.NoType)
          case LookupResult.LookupFailure(err) =>
            Reporter.appendError(err)
            errorPair
        }
      case _: Symbol.TypeParamSymbol =>
        typedSuffix.tpe.asRefType.lookupType(select.name) match {
          case LookupResult.LookupSuccess(symbol) => (symbol, Type.RefType(symbol, Vector.empty, Vector.empty))
          case LookupResult.LookupFailure(err) =>
            Reporter.appendError(err)
            errorPair
        }
      case _ => throw new ImplementationErrorException("unexpected to reach here")
    }

    val (assignedSymbol, assignedType) = symbol match {
      case sym: Symbol.TypeSymbol => (sym, tpe)
      case sym: Symbol.PackageSymbol if acceptPkg => (sym, tpe)
      case sym: Symbol.PackageSymbol =>
        Reporter.appendError(Error.RequireSymbol[Symbol.TypeSymbol](sym))
        (Symbol.ErrorSymbol, Type.ErrorType)
      case sym => (sym, tpe)
    }

    StaticSelect(typedSuffix, select.name)
      .setTpe(tpe)
      .setSymbol(assignedSymbol)
      .setID(select.id)
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

  def typedHardwareParamExpr(expr: Expression)(implicit ctx: Context.NodeContext): Expression = expr match {
    case ident: Ident => typedHardwareParamIdent(ident)
    case binop: BinOp => typedHardwareParamBinOp(binop)
    case literal: IntLiteral => typedHardwareParamIntLit(literal)
    case literal: StringLiteral => typedHardwareParamStrLit(literal)
    case expr => throw new ImplementationErrorException(s"${expr.getClass} should not appear here")
  }

  def typedHardwareParamIdent(ident: Ident)(implicit ctx: Context.NodeContext): Ident = {
    def verifyType(symbol: Symbol): Either[Error, Unit] =
      if(symbol.tpe =:= Type.numTpe || symbol.tpe =:= Type.strTpe) Right(())
      else Left(Error.RequireSpecificType(
        Vector(Type.numTpe, Type.strTpe), symbol.tpe
      ))

    val symbol = for {
      symbol <- ctx.lookup[Symbol.TermSymbol](ident.name).toEither
           _ <- verifyType(symbol)
    } yield symbol

    symbol match {
      case Left(err) =>
        Reporter.appendError(err)
        ident.setTpe(Type.ErrorType).setSymbol(Symbol.ErrorSymbol)
      case Right(symbol) =>
        ident.setTpe(symbol.tpe).setSymbol(symbol)
    }
  }

  def typedHardwareParamBinOp(binop: BinOp)(implicit ctx: Context.NodeContext): BinOp = {
    val typedLeft  = typedHardwareParamExpr(binop.left)
    val typedRight = typedHardwareParamExpr(binop.right)

    val isValid = (typedLeft.tpe =:= Type.numTpe) && (typedRight.tpe =:= Type.numTpe)
    val hasStrTpe = (typedLeft.tpe =:= Type.strTpe) || (typedRight.tpe =:= Type.strTpe)
    val tpe =
      if(isValid) Type.numTpe
      else if(hasStrTpe) { Reporter.appendError(Error.SymbolNotFound("+")); Type.ErrorType }
      else Type.ErrorType

    BinOp(binop.op, typedLeft, typedRight).setTpe(tpe).setID(binop.id)
  }

  def typedHardwareParamIntLit(int: IntLiteral): IntLiteral = {
    int.setTpe(Type.numTpe)
  }

  def typedHardwareParamStrLit(str: StringLiteral): StringLiteral = {
    str.setTpe(Type.strTpe)
  }


  def typedFinish(finish: Finish)(implicit ctx: Context.NodeContext): Finish = {
    ctx.owner match {
      case _: Symbol.StateSymbol =>
      case _: Symbol.StageSymbol =>
      case _ => Reporter.appendError(Error.FinishOutsideStage)
    }

    finish.setTpe(Type.unitTpe).setID(finish.id)
  }

  def typedGoto(goto: Goto)(implicit ctx: Context.NodeContext): Goto = {
    ctx.owner match {
      case _: Symbol.StateSymbol =>
        ctx.lookup[Symbol.StateSymbol](goto.target) match {
          case LookupResult.LookupFailure(err) => Reporter.appendError(err)
          case _ =>
        }
      case _ => Reporter.appendError(Error.GotoOutsideState)
    }

    goto.setTpe(Type.unitTpe).setID(goto.id)
  }

  def typedGenerate(generate: Generate)(implicit ctx: Context.NodeContext): Generate = {
    val tpe = ctx.lookup[Symbol.StageSymbol](generate.target) match {
      case LookupResult.LookupFailure(err) =>
        Reporter.appendError(err)
        Type.ErrorType
      case LookupResult.LookupSuccess(symbol) =>
        val tpe = symbol.tpe.asMethodType
        val typedArgs = generate.params.map(typedExpr)

        verifyParamTypes(tpe.params, typedArgs.map(_.tpe)).foreach(Reporter.appendError)
        tpe.returnType
    }

    generate.setTpe(tpe)
  }

  def typedRelay(relay: Relay)(implicit ctx: Context.NodeContext): Relay = {
    ctx.owner match {
      case _: Symbol.StageSymbol =>
      case _: Symbol.StateSymbol =>
      case _ => Reporter.appendError(Error.RelayOutsideStage)
    }

    val tpe = ctx.lookup[Symbol.StageSymbol](relay.target) match {
      case LookupResult.LookupFailure(err) =>
        Reporter.appendError(err)
        Type.ErrorType
      case LookupResult.LookupSuccess(symbol) =>
        val tpe = symbol.tpe.asMethodType
        val typedArgs = relay.params.map(typedExpr)

        verifyParamTypes(tpe.params, typedArgs.map(_.tpe)).foreach(Reporter.appendError)

        tpe.returnType
    }

    relay.setTpe(tpe)
  }

  def verifyParamTypes(expect: Vector[Type], actual: Vector[Type])(implicit ctx: Context.NodeContext): Vector[Error] = {
    if (expect.length != actual.length)
      return Vector(Error.ParameterLengthMismatch(expect.length, actual.length))

    (expect zip actual)
      .collect { case (e: Type.RefType, a: Type.RefType) => (e, a) }
      .filter { case (e, a) => a <|= e }
      .map { case (e, a) => Error.TypeMissmatch(e, a) }
  }

  def verifyParamType(expect: Type, actual: Type)(implicit ctx: Context.NodeContext): Vector[Error] =
    verifyParamTypes(Vector(expect), Vector(actual))

  def verifyTypeParams(
    symbol: Symbol.TypeSymbol,
    hps: Vector[Expression],
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
}

object TypedCache {
  import scala.collection.mutable

  private val cache = mutable.Map[Int, AST]()

  def setTree(tree: AST): Unit = {
    cache(tree.id) = tree
  }

  def getTree(tree: AST): Option[AST] = cache.get(tree.id)
}
