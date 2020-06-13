package tchdl.typecheck

import tchdl.ast._
import tchdl.util.TchdlException.ImplementationErrorException
import tchdl.util._

object Typer {
  def exec(cu: CompilationUnit)(implicit global: GlobalData): CompilationUnit = {
    val ctx = global.rootPackage.search(cu.pkgName)
      .getOrElse(throw new ImplementationErrorException(s"${cu.pkgName} should be there"))
      .lookupCtx(cu.filename.get)
      .getOrElse(throw new ImplementationErrorException(s"${cu.filename.get}'s context should be there'"))

    val topDefs = cu.topDefs.map(typedTopLevelDefinition(_)(ctx, global))

    CompilationUnit(cu.filename, cu.pkgName, cu.imports, topDefs)
  }

  def typedTopLevelDefinition(ast: Definition)(implicit ctx: Context.RootContext, global: GlobalData): Definition = ast match {
    case module: ModuleDef => typedModuleDef(module)
    case struct: StructDef => typedStructDef(struct)
    case implClass: ImplementClass => typedImplementClass(implClass)
    case implInterface: ImplementInterface => typedImplementInterface(implInterface)
    case deftree =>
      val msg = s"typed [${deftree.getClass.getName}] at top level but it is invalid"
      throw new ImplementationErrorException(msg)
  }

  def typedDefinition(ast: Definition)(implicit ctx: Context.NodeContext, global: GlobalData): Definition = ast match {
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

  def typedModuleDef(module: ModuleDef)(implicit ctx: Context.RootContext, global: GlobalData): ModuleDef = {
    module.symbol.tpe

    val interfaceCtx = Context(ctx, module.symbol)
    interfaceCtx.reAppend(module.hp.map(_.symbol) ++ module.tp.map(_.symbol): _*)

    val typedHp = module.hp.map(typedValDef(_)(interfaceCtx, global))
    val typedTp = module.tp.map(typedTypeDef(_)(interfaceCtx, global))

    val typedParents = module.parents.map(typedValDef(_)(interfaceCtx, global))
    val typedSiblings = module.siblings.map(typedValDef(_)(interfaceCtx, global))

    val typedModule = module.copy(
      module.name,
      typedHp,
      typedTp,
      module.bounds,
      typedParents,
      typedSiblings
    )
      .setSymbol(module.symbol)
      .setID(module.id)

    global.cache.set(typedModule)
    typedModule
  }

  def typedStructDef(struct: StructDef)(implicit ctx: Context, global: GlobalData): StructDef = {
    struct.symbol.tpe

    val signatureCtx = Context(ctx, struct.symbol)
    ctx.reAppend(
      struct.hp.map(_.symbol) ++
        struct.tp.map(_.symbol): _*
    )

    val typedHp = struct.hp.map(typedValDef(_)(signatureCtx, global))
    val typedTp = struct.tp.map(typedTypeDef(_)(signatureCtx, global))

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
  }

  def typedImplementClass(impl: ImplementClass)(implicit ctx: Context.RootContext, global: GlobalData): ImplementClass = {
    val signatureCtx = Context(ctx, impl.symbol)

    signatureCtx.reAppend(
      impl.hp.map(_.symbol) ++
      impl.tp.map(_.symbol) :_*
    )

    val typedHp = impl.hp.map(typedValDef(_)(signatureCtx, global))
    val typedTp = impl.tp.map(typedTypeDef(_)(signatureCtx, global))

    val typedTarget = typedTypeTree(impl.target)(signatureCtx, global)
    typedTarget.tpe match {
      case Type.ErrorType => impl
      case targetTpe: Type.RefType =>
        val implCtx = Context(signatureCtx, targetTpe)
        implCtx.reAppend(
          impl.methods.map(_.symbol) ++
          impl.stages.map(_.symbol): _*
        )

        val typedMethods = impl.methods.map(typedMethodDef(_)(implCtx, global))
        val typedStages = impl.stages.map(typedStageDef(_)(implCtx, global))

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

        global.cache.set(typedImpl)
        typedImpl
    }
  }

  def typedImplementInterface(impl: ImplementInterface)(implicit ctx: Context.RootContext, global: GlobalData): ImplementInterface = {
    val signatureCtx = Context(ctx, impl.symbol)
    signatureCtx.reAppend(
      impl.hp.map(_.symbol) ++
      impl.tp.map(_.symbol): _*
    )

    val typedHp = impl.hp.map(Typer.typedValDef(_)(signatureCtx, global))
    val typedTp = impl.tp.map(Typer.typedTypeDef(_)(signatureCtx, global))

    val typedInterface = typedTypeTree(impl.interface)(signatureCtx, global)
    val typedTarget = typedTypeTree(impl.target)(signatureCtx, global)

    typedTarget.tpe match {
      case Type.ErrorType => impl
      case targetTpe: Type.RefType =>
        val implCtx = Context(signatureCtx, targetTpe)
        implCtx.reAppend(impl.methods.map(_.symbol): _*)

        val typedMethods = impl.methods.map(Typer.typedMethodDef(_)(implCtx, global))

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

        global.cache.set(typedImpl)

        typedImpl
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

  def typedMethodDef(method: MethodDef)(implicit ctx: Context.NodeContext, global: GlobalData): MethodDef = {
    method.symbol.tpe

    val signatureCtx = Context(ctx, method.symbol)
    ctx.reAppend(
      method.hp.map(_.symbol) ++
      method.tp.map(_.symbol) ++
      method.params.map(_.symbol): _*
    )

    val typedHp = method.hp.map(typedValDef(_)(signatureCtx, global))
    val typedTp = method.tp.map(typedTypeDef(_)(signatureCtx, global))
    val typedParams = method.params.map(typedValDef(_)(signatureCtx, global))
    val typedRetTpe = typedTypeTree(method.retTpe)(signatureCtx, global)
    val typedBlk = method.blk.map(typedBlock(_)(signatureCtx, global))

    typedBlk.foreach(global.cache.set)

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

    global.cache.set(typedMethod)
    typedMethod
  }

  def typedValDef(vdef: ValDef)(implicit ctx: Context.NodeContext, global: GlobalData): ValDef = {
    vdef.symbol.tpe

    val typedTpeTree = vdef.tpeTree.map(typedTypeTree)
    val typedExp = vdef.expr.map(typedExpr)

    val typedValDef = vdef.copy(
      vdef.flag,
      vdef.name,
      typedTpeTree,
      typedExp
    )
      .setSymbol(vdef.symbol)
      .setID(vdef.id)

    typedExp.foreach(global.cache.set)
    global.cache.set(typedValDef)
    typedValDef
  }

  def typedStageDef(stage: StageDef)(implicit ctx: Context.NodeContext, global: GlobalData): StageDef = {
    stage.symbol.tpe

    val signatureCtx = Context(ctx, stage.symbol)
    ctx.reAppend(stage.params.map(_.symbol): _*)

    val typedParams = stage.params.map(typedValDef(_)(signatureCtx, global))
    val typedRetTpe = typedTypeTree(stage.retTpe)(signatureCtx, global)

    val blkCtx = Context.blk(signatureCtx)
    stage.blk.map(Namer.nodeLevelNamed(_)(blkCtx, global))
    stage.states.map(Namer.nodeLevelNamed(_)(blkCtx, global))

    val typedBlkElems = stage.blk.map {
      case vdef: ValDef => typedValDef(vdef)(blkCtx, global)
      case expr: Expression => typedExpr(expr)(blkCtx, global)
    }

    val typedStates = stage.states.map(typedStateDef(_)(blkCtx, global))

    val typedStage = stage.copy(
      stage.name,
      typedParams,
      typedRetTpe,
      typedStates,
      typedBlkElems
    )
      .setSymbol(stage.symbol)
      .setID(stage.id)

    global.cache.set(typedStage)
    typedStage
  }

  def typedStateDef(state: StateDef)(implicit ctx: Context.NodeContext, global: GlobalData): StateDef = {
    val stateCtx = Context(ctx, state.symbol)
    val typedBlk = typedBlock(state.blk)(stateCtx, global)

    val typedState = state.copy(state.name, typedBlk)
      .setSymbol(state.symbol)
      .setID(state.id)

    global.cache.set(typedState)
    typedState
  }

  def typedTypeDef(tpeDef: TypeDef)(implicit ctx: Context.NodeContext, global: GlobalData): TypeDef = {
    Namer.nodeLevelNamed(tpeDef, ctx)

    tpeDef.symbol.tpe

    val typedTpeDef = tpeDef.copy(tpeDef.name)
      .setSymbol(tpeDef.symbol)
      .setID(tpeDef.id)

    global.cache.set(typedTpeDef)
    typedTpeDef
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
      case _: ApplyParams =>
        throw new ImplementationErrorException("ApplyParams tree should not be typed")
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
            else Left(Error.TypeMissmatch(p, a))
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
        leftTpe.lookupOperation(binop.op, rightTpe, ctx.hpBounds, ctx.tpBounds, ctx)
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
      case vdef: ValDef => typedValDef(vdef)(blkCtx, global)
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
      global.repo.error.append(Error.RequireBooleanType(typedCond.tpe))

    typedAlt match {
      case None =>
        IfExpr(typedCond, typedConseq, typedAlt).setTpe(Type.unitTpe).setID(ifexpr.id)
      case Some(alt) =>
        val retTpe = (alt.tpe, typedConseq.tpe) match {
          case (Type.ErrorType, tpe) => tpe
          case (tpe, Type.ErrorType) => tpe
          case (altTpe, conseqTpe)  =>
            if(altTpe =!= conseqTpe)
              global.repo.error.append(Error.TypeMissmatch(altTpe, conseqTpe))

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

  /*
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
 */

  /*
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
   */

  def typedBitLiteral(bit: BitLiteral)(implicit ctx: Context.NodeContext, global: GlobalData): BitLiteral = {
    val length = IntLiteral(bit.length).setTpe(Type.numTpe)
    val bitTpe = Type.bitTpe(length)

    bit.setTpe(bitTpe).setID(bit.id)
  }

  def typedIntLiteral(int: IntLiteral)(implicit ctx: Context.NodeContext, global: GlobalData): IntLiteral = {
    val intSymbol = global.builtin.lookup("Int")
    val intTpe = Type.RefType(intSymbol)

    int.setTpe(intTpe).setID(int.id)
  }

  def typedUnitLiteral(unit: UnitLiteral)(implicit ctx: Context.NodeContext, global: GlobalData): UnitLiteral = {
    val unitSymbol = global.builtin.lookup("Unit")
    val unitTpe = Type.RefType(unitSymbol)

    unit.setTpe(unitTpe).setID(unit.id)
  }

  def typedStringLiteral(str: StringLiteral)(implicit ctx: Context.NodeContext, global: GlobalData): StringLiteral = {
    val strSymbol = global.builtin.lookup("String")
    val strTpe = Type.RefType(strSymbol)

    str.setTpe(strTpe).setID(str.id)
  }

  def typedHPExpr(expr: HPExpr)(implicit ctx: Context.NodeContext, global: GlobalData): HPExpr = expr match {
    case ident: Ident => typedHPIdent(ident)
    case binop: HPBinOp => typedHPBinOp(binop)
    case literal: IntLiteral => typedHPIntLit(literal)
    case literal: StringLiteral => typedHPStrLit(literal)
  }

  def typedHPIdent(ident: Ident)(implicit ctx: Context.NodeContext, global: GlobalData): Ident = {
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

  def verifyParamTypes(expect: Vector[Type], actual: Vector[Type])(implicit ctx: Context.NodeContext, global: GlobalData): Vector[Error] = {
    if (expect.length != actual.length)
      return Vector(Error.ParameterLengthMismatch(expect.length, actual.length))

    (expect zip actual)
      .collect { case (e: Type.RefType, a: Type.RefType) => (e, a) }
      .filter { case (e, a) => a =:= e }
      .map { case (e, a) => Error.TypeMissmatch(e, a) }
  }

  def verifyParamType(expect: Type, actual: Type)(implicit ctx: Context.NodeContext, global: GlobalData): Vector[Error] =
    verifyParamTypes(Vector(expect), Vector(actual))

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
