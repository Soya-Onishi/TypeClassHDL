package tchdl.backend

import tchdl.backend.{ast => backend}
import tchdl.{ast => frontend}
import tchdl.util._
import tchdl.util.TchdlException.ImplementationErrorException

import scala.annotation.tailrec
import scala.collection.immutable.ListMap


object BackendIRGen {
  case class Summary(modules: Vector[ModuleContainer], methods: Vector[MethodContainer], labels: Set[BackendLabel])

  def exec(modules: Vector[BuiltModule])(implicit global: GlobalData): (Vector[ModuleContainer], Vector[MethodContainer]) = {
    val (moduleContainers, moduleMethodss, labels) = modules.filter(_.module.symbol != Symbol.mem).map(buildModule).unzip3
    val labelSet = labels.flatten.toSet

    val initSummary = Summary(moduleContainers, moduleMethodss.flatten, labelSet)
    val summary = build(initSummary)

    (summary.modules, summary.methods)
  }

  private def isInterface(symbol: Symbol.MethodSymbol): Boolean =
    symbol.hasFlag(Modifier.Input) ||
    symbol.hasFlag(Modifier.Internal) ||
    symbol.hasFlag(Modifier.Parent) ||
    symbol.hasFlag(Modifier.Sibling)

  @tailrec def build(summary: Summary)(implicit global: GlobalData): Summary = {
    def makeContext(label: BackendLabel, impl: Option[Symbol.ImplementSymbol], method: Option[Symbol.MethodSymbol]): BackendContext = {
      def makeTPBound(symbol: Symbol with HasParams): Map[Type.RefType, Vector[BackendType]] = {
        val tpBounds = symbol.tpBound.map {
          tpBound => tpBound.target -> tpBound.bounds.map(toBackendType(_, label.hps, label.tps))
        }

        tpBounds.toMap
      }

      val implTPBound = impl.map(makeTPBound).toVector
      val methodTPBound = method.map(makeTPBound).toVector
      val tpBound = (implTPBound ++ methodTPBound).flatten.toMap

      BackendContext(label, tpBound)
    }

    val interfaceContainers = summary.modules.flatMap(_.interfaces)
    val stageContainers = summary.modules.flatMap(_.stages)

    val unConstructedLabels = summary.labels.filterNot {
      case label: MethodLabel if isInterface(label.symbol) => interfaceContainers.exists(_.label == label)
      case label: MethodLabel => summary.methods.exists(_.label == label)
      case label: StageLabel => stageContainers.exists(_.label == label)
    }

    val renewedSummary = unConstructedLabels.foldLeft(summary) {
      case (summary, label: MethodLabel) if isInterface(label.symbol) =>
        val impl =
          findImplClassTree(label.symbol, global) orElse
            findImplInterfaceTree(label.symbol, global) getOrElse (throw new ImplementationErrorException("method must be there"))
        val method = findMethodTree(label.symbol, global).getOrElse(throw new ImplementationErrorException("method tree should be found"))

        val context = makeContext(label, Some(impl.symbol.asImplementSymbol), None)
        val (container, labels) = buildMethod(method, label)(context, global)

        val modules = summary.modules.map {
          case module if label.accessor.contains(module.tpe) => module.addInterface(container)
          case module => module
        }

        Summary(modules, summary.methods, summary.labels ++ labels)
      case (summary, label: MethodLabel) =>
        val impl = findImplClassTree(label.symbol, global) orElse findImplInterfaceTree(label.symbol, global)
        val method = findMethodTree(label.symbol, global).getOrElse(throw new ImplementationErrorException("method tree should be found"))
        val context = makeContext(label, impl.map(_.symbol.asImplementSymbol), Some(method.symbol.asMethodSymbol))
        val (container, labels) = buildMethod(method, label)(context, global)

        Summary(summary.modules, summary.methods :+ container, summary.labels ++ labels)
      case (summary, label: StageLabel) =>
        val impl =
          findImplClassTree(label.symbol, global) orElse
            findImplInterfaceTree(label.symbol, global) getOrElse (throw new ImplementationErrorException("method must be there"))
        val stage = findStageTree(label.symbol, global).getOrElse(throw new ImplementationErrorException("stage tree should be found"))

        val context = makeContext(label, Some(impl.symbol.asImplementSymbol), None)

        val (container, labels) = buildStage(stage, label)(context, global)

        val modules = summary.modules.map {
          case module if label.accessor.contains(module.tpe) => module.addStage(container)
          case module => module
        }

        Summary(modules, summary.methods, summary.labels ++ labels)
    }

    if (unConstructedLabels.isEmpty) renewedSummary
    else build(renewedSummary)
  }

  def buildModule(builtModule: BuiltModule)(implicit global: GlobalData): (ModuleContainer, Vector[MethodContainer], Set[BackendLabel]) = {
    builtModule.impl match {
      case None =>
        val moduleContainer = ModuleContainer.empty(builtModule.module, Map.empty)
        (moduleContainer, Vector.empty, Set.empty)
      case Some(impl) =>
        val hpTable = buildHPTable(impl.symbol.hps, builtModule.module, impl.targetType)
        val tpTable = buildTPTable(impl.symbol.tps, builtModule.module, impl.targetType)
        val tpBound = {
          val tpBounds = impl.symbol.tpBound.map {
            tpBound =>
              val bounds = tpBound.bounds.map(toBackendType(_, hpTable, tpTable))
              tpBound.target -> bounds
          }

          tpBounds.toMap
        }

        val containerHPs = hpTable.map { case (hp, elem) => hp.path.rootPath.last + "$" + hp.path.innerPath.mkString("$") -> elem }
        val moduleContainer = ModuleContainer.empty(builtModule.module, containerHPs)

        val implTree = findImplClassTree(impl.symbol.asImplementSymbol, global).getOrElse(throw new ImplementationErrorException("impl tree should be found"))
        val module = moduleContainer.tpe

        val pairs = implTree.components.collect {
          case method: frontend.MethodDef if isInterface(method.symbol.asMethodSymbol) =>
            val label = MethodLabel(method.symbol.asMethodSymbol, Some(module), None, hpTable, tpTable)
            val context = BackendContext(label, tpBound)
            val (container, labels) = buildMethod(method, label)(context, global)

            (container, labels)
          case stage: frontend.StageDef =>
            val label = StageLabel(stage.symbol.asStageSymbol, Some(module), hpTable, tpTable)
            val context = BackendContext(label, tpBound)
            val (container, labels) = buildStage(stage, label)(context, global)

            (container, labels)
          case always: frontend.AlwaysDef =>
            val label = AlwaysLabel(always.symbol.asAlwaysSymbol, Some(module), hpTable, tpTable)
            val context = BackendContext(label, tpBound)
            val BuildResult(nodes, Some(last), labels) = buildBlk(always.blk)(context, global)

            val code = nodes :+ backend.Abandon(last)
            val container = AlwaysContainer(always.symbol.asAlwaysSymbol, code)

            (container, labels)
          case vdef: frontend.ValDef =>
            val label = FieldLabel(vdef.symbol.asVariableSymbol, Some(module), hpTable, tpTable)
            val context = BackendContext(label, tpBound)

            val exprResult =
              if (vdef.flag.hasNoFlag(Modifier.Child)) {
                vdef.expr
                  .map(buildExpr(_)(context, global))
                  .getOrElse(BuildResult(Vector.empty, None, Set.empty))
              } else {
                val Some(construct: frontend.ConstructModule) = vdef.expr
                buildConstructModule(construct, Some(vdef.name))(context, global)
              }

            val tpe = toBackendType(vdef.symbol.tpe.asRefType, hpTable, tpTable)

            val container = FieldContainer(
              vdef.flag,
              label,
              exprResult.nodes,
              exprResult.last,
              tpe
            )

            (container, exprResult.labels)
        }

        val (containers, labels) = pairs.unzip
        val labelSet = labels.flatten.toSet
        val (assignedModule, moduleMethods) = containers.foldLeft((moduleContainer, Vector.empty[MethodContainer])) {
          case ((module, methods), c: MethodContainer) if isInterface(c.label.symbol) => (module.addInterface(c), methods)
          case ((module, methods), c: MethodContainer) => (module, methods :+ c)
          case ((module, methods), c: StageContainer) => (module.addStage(c), methods)
          case ((module, methods), c: AlwaysContainer) => (module.addAlways(c), methods)
          case ((module, methods), c: FieldContainer) => (module.addField(c), methods)
        }

        (assignedModule, moduleMethods, labelSet)
    }
  }

  def buildMethod(methodDef: frontend.MethodDef, label: MethodLabel)(implicit ctx: BackendContext, global: GlobalData): (MethodContainer, Set[BackendLabel]) = {
    val methodName = label.toString

    val hparamNames = methodDef.hp.map(hp => methodName + "$" + hp.name)
    val hparamTpes = methodDef.hp.view.map(_.symbol.tpe.asRefType).map(toBackendType(_, label.hps, label.tps))
    val hparams = ListMap.from(hparamNames zip hparamTpes)
    val hparamSymbols = methodDef.hp.map(_.symbol.asHardwareParamSymbol)
    (hparamSymbols zip hparamNames).foreach { case (symbol, name) => ctx.append(symbol, name) }

    val paramNames = methodDef.params.map(param => methodName + "$" + param.name)
    val paramTpes = methodDef.params.map(_.symbol.tpe.asRefType).map(toBackendType(_, label.hps, label.tps))
    val params = ListMap.from(paramNames zip paramTpes)
    val paramSymbols = methodDef.params.map(_.symbol.asVariableSymbol)
    (paramSymbols zip paramNames).foreach { case (symbol, name) => ctx.append(symbol, name) }

    val blk = methodDef.blk.getOrElse(throw new ImplementationErrorException("impl's method should have body"))
    val BuildResult(nodes, Some(expr), labels) = buildExpr(blk)

    val retTpe = toBackendType(methodDef.symbol.tpe.asMethodType.returnType, ctx.hpTable, ctx.tpTable)

    (MethodContainer(label, hparams, params, nodes, expr, retTpe), labels)
  }

  def buildStage(stageDef: frontend.StageDef, stageLabel: StageLabel)(implicit ctx: BackendContext, global: GlobalData): (StageContainer, Set[BackendLabel]) = {
    val paramNames = stageDef.params.map(param => ctx.label.toString + "$" + param.name)
    val paramTpes = stageDef.params.view.map(_.symbol.tpe.asRefType).map(toBackendType(_, ctx.hpTable, ctx.tpTable))
    val params = ListMap.from(paramNames zip paramTpes)
    val paramSymbols = stageDef.params.map(_.symbol.asVariableSymbol)

    (paramSymbols zip paramNames).foreach { case (symbol, name) => ctx.append(symbol, name) }

    val BuildResult(blkNodes, None, blkLabels) = stageDef.blk
      .map(buildBlockElem(_)(ctx, global))
      .foldLeft(BuildResult(Vector.empty, None, Set.empty)) {
        case (summary, result) =>
          BuildResult(
            summary.nodes ++ result.nodes,
            None,
            summary.labels ++ result.labels
          )
      }

    val stateSymbols = stageDef.symbol.tpe.declares
      .toMap.values
      .collect { case state: Symbol.StateSymbol => state }
      .toVector
      .sortWith { case (left, right) => left.name < right.name }

    val (states, labelsFromState) = stateSymbols.zipWithIndex.map {
      case (state, idx) =>
        val label = StateLabel(state, stageLabel.accessor, stageLabel, idx, stageLabel.hps, stageLabel.tps)
        val context = BackendContext(ctx, label)
        val stateDef = stageDef.states.find(_.symbol == state).get

        buildState(stateDef, label)(context, global)
    }.unzip

    val retTpe = stageDef.symbol.tpe.asMethodType.returnType
    val backendTpe = toBackendType(retTpe, ctx.hpTable, ctx.tpTable)

    (StageContainer(stageLabel, params, states, blkNodes, backendTpe), blkLabels ++ labelsFromState.flatten)
  }

  def buildState(stateDef: frontend.StateDef, label: StateLabel)(implicit ctx: BackendContext, global: GlobalData): (StateContainer, Set[BackendLabel]) = {
    val paramNames = stateDef.params.map(_.name).map(param => label.toString + "$" + param)
    val paramTpes = stateDef.params.map(_.symbol.tpe.asRefType).map(toBackendType(_, ctx.hpTable, ctx.tpTable))
    val paramSymbols = stateDef.params.map(_.symbol.asTermSymbol)
    (paramSymbols zip paramNames).foreach { case (symbol, name) => ctx.append(symbol, name) }

    val BuildResult(nodes, last, labels) = buildBlk(stateDef.blk)
    val lastStmt = last.map(backend.Abandon.apply).getOrElse(backend.Abandon(backend.UnitLiteral()))
    val params = ListMap.from(paramNames zip paramTpes)

    val code = nodes :+ lastStmt

    (StateContainer(label, params, code), labels)
  }

  def buildExpr(expr: frontend.Expression)(implicit ctx: BackendContext, global: GlobalData): BuildResult =
    expr match {
      case ident: frontend.Ident => buildIdent(ident)
      case select: frontend.Select => buildSelect(select)
      case apply: frontend.Apply => buildApply(apply)
      case binop: frontend.StdBinOp => buildBinOp(binop)
      case unaryOp: frontend.StdUnaryOp => buildUnaryOp(unaryOp)
      case blk: frontend.Block => buildBlk(blk)
      case matchExpr: frontend.Match => buildMatch(matchExpr)
      case construct: frontend.ConstructClass => buildConstructClass(construct)
      case construct: frontend.ConstructModule => buildConstructModule(construct, None)
      case construct: frontend.ConstructEnum => buildConstructEnum(construct)
      case ifexpr: frontend.IfExpr => buildIfExpr(ifexpr)
      case ths: frontend.This => buildThis(ths)
      case _: frontend.Finish => buildFinish
      case goto: frontend.Goto => buildGoto(goto)
      case generate: frontend.Generate => buildGenerate(generate)
      case relay: frontend.Relay => buildRelay(relay)
      case ret: frontend.Return => buildReturn(ret)
      case cast: frontend.CastExpr => buildExpr(cast.expr)
      case frontend.IntLiteral(value) => BuildResult(backend.IntLiteral(value))
      case frontend.BitLiteral(value, length) => BuildResult(backend.BitLiteral(value, HPElem.Num(length)))
      case frontend.UnitLiteral() => BuildResult(backend.UnitLiteral())
    }

  def buildIdent(ident: frontend.Ident)(implicit ctx: BackendContext, global: GlobalData): BuildResult = {
    val name = ctx.lookup(ident.symbol.asTermSymbol)
    val tpe = toBackendType(ident.tpe.asRefType, ctx.hpTable, ctx.tpTable)
    val term = backend.Term.Variable(name, tpe)

    BuildResult(Vector.empty, Some(backend.Ident(term, tpe)), Set.empty)
  }

  def buildSelect(select: frontend.Select)(implicit ctx: BackendContext, global: GlobalData): BuildResult = {
    val selectRefTpe = select.tpe.asRefType
    val selectTpe = toBackendType(selectRefTpe, ctx.hpTable, ctx.tpTable)

    val BuildResult(nodes, Some(last), labels) = buildExpr(select.prefix)
    val node = backend.Temp(ctx.temp.get(), last)
    val label = FieldLabel(select.symbol.asVariableSymbol, Some(last.tpe), ListMap.empty, ListMap.empty)
    val refer = backend.ReferField(backend.Term.Temp(node.id, last.tpe), label, selectTpe)

    BuildResult(nodes :+ node, Some(refer), labels)
  }

  def buildApply(apply: frontend.Apply)(implicit ctx: BackendContext, global: GlobalData): BuildResult = {
    case class Summary(nodes: Vector[backend.Stmt], terms: Vector[backend.Term.Temp], labels: Set[BackendLabel])

    def lookupImplMethod(
      accessor: Type.RefType,
      replacedAccessor: Type.RefType,
      hargs: Vector[HPElem],
      targs: Vector[BackendType],
      args: Vector[BackendType],
      methodName: String,
      requireStatic: Boolean
    ): Symbol.MethodSymbol = {
      val bounds = accessor.castedAs match {
        case None => ctx.tpBound.getOrElse(accessor, Vector.empty).map(toRefType)
        case Some(tpe) => Vector(tpe)
      }

      val callerHP = hargs.map {
        case HPElem.Num(value) => frontend.IntLiteral(value)
        case HPElem.Str(value) => frontend.StringLiteral(value)
      }
      val callerTP = targs.map(toRefType)
      val argTpes = args.map(toRefType)

      val (methodSymbol, _) = replacedAccessor
        .lookupMethodFromBounds(
          argTpes,
          callerHP,
          callerTP,
          bounds,
          methodName,
          requireStatic
        )

      methodSymbol
    }

    val argSummary = apply.args.foldLeft(Summary(Vector.empty, Vector.empty, Set.empty)) {
      case (summary, arg) =>
        val BuildResult(nodes, Some(expr), labels) = buildExpr(arg)
        val node = backend.Temp(ctx.temp.get(), expr)

        val newTemps = summary.nodes ++ nodes :+ node
        val newTerms = summary.terms :+ backend.Term.Temp(node.id, expr.tpe)

        Summary(newTemps, newTerms, labels)
    }

    val retTpe = toBackendType(apply.tpe.asRefType, ctx.hpTable, ctx.tpTable)
    val hargs = apply.hps.map(evalHPExpr(_, ctx.hpTable))
    val targs = apply.tps.view
      .map(_.tpe.asRefType)
      .map(toBackendType(_, ctx.hpTable, ctx.tpTable))
      .toVector


    apply.prefix match {
      case ident @ frontend.Ident(name) =>
        val pkg = ident.symbol.path.pkgName
        val name = ident.symbol.name
        val args = argSummary.terms.map(_.tpe.symbol).map(SigArg.Sym.apply)
        val signature = FunctionSignature(pkg, name, None, args: _*)
        val isBuiltIn = builtinFunctions.contains(signature)

        val (call, label) = if(isBuiltIn) {
          val call = backend.CallBuiltIn(signature.toString, None, argSummary.terms, hargs, retTpe)
          (call, None)
        } else {
          val label = makeLabel(ident.symbol.asMethodSymbol, None, argSummary.terms.map(_.tpe), hargs, targs)
          val call = backend.CallMethod(label, None, hargs, argSummary.terms, retTpe)

          (call, Some(label))
        }

        val labels = argSummary.labels ++ label

        BuildResult(argSummary.nodes, Some(call), labels)
      case select @ frontend.StaticSelect(prefix, methodName) =>
        val prefixTpe = prefix.tpe.asRefType
        val prefixBackendTpe = toBackendType(prefixTpe, ctx.hpTable, ctx.tpTable)
        val castBackendTpe = prefixTpe.castedAs.map(toBackendType(_, ctx.hpTable, ctx.tpTable))
        val selectMethodSymbol = select.symbol.asMethodSymbol

        val referredMethodSymbol = (findImplClassTree(selectMethodSymbol, global), findImplInterfaceTree(selectMethodSymbol, global)) match {
          case (Some(_), _) => selectMethodSymbol
          case (None, Some(_)) => selectMethodSymbol
          case (None, None) =>
            val replacedType =
              castBackendTpe.map(toRefType) match {
                case Some(casted) => Type.RefType.cast(toRefType(prefixBackendTpe), casted)
                case None => toRefType(prefixBackendTpe)
              }

            lookupImplMethod(prefixTpe, replacedType, hargs, targs, argSummary.terms.map(_.tpe), methodName, requireStatic = true)
        }

        val pkg = referredMethodSymbol.path.pkgName
        val name = referredMethodSymbol.name
        val args = argSummary.terms.map(_.tpe.symbol).map(SigArg.Sym.apply)
        val signature = FunctionSignature(pkg, name, Some(prefixTpe.origin), args: _*)
        val isBuiltIn = builtinFunctions.contains(signature)

        val (call, label) = if(isBuiltIn) {
          val call = backend.CallBuiltIn(signature.toString, Some(prefixBackendTpe), argSummary.terms, hargs, retTpe)

          (call, None)
        } else {
          val label = makeLabel(referredMethodSymbol, Some(prefixBackendTpe), argSummary.terms.map(_.tpe), hargs, targs)
          val call = backend.CallMethod(label, None, hargs, argSummary.terms, retTpe)

          (call, Some(label))
        }

        val labels = label.map(argSummary.labels + _).getOrElse(argSummary.labels)

        BuildResult(argSummary.nodes, Some(call), labels)
      case select @ frontend.Select(prefix, methodName) =>
        val BuildResult(nodes, Some(last), labels) = buildExpr(prefix)
        val accessorNode = backend.Temp(ctx.temp.get(), last)
        val accessor = backend.Term.Temp(accessorNode.id, last.tpe)
        val isInterface =
          select.symbol.hasFlag(Modifier.Input) ||
          select.symbol.hasFlag(Modifier.Internal) ||
          select.symbol.hasFlag(Modifier.Parent) ||
          select.symbol.hasFlag(Modifier.Sibling)


        val selectMethodSymbol = select.symbol.asMethodSymbol
        val referredMethodSymbol = (findImplClassTree(selectMethodSymbol, global), findImplInterfaceTree(selectMethodSymbol, global)) match {
          case (Some(_), _) => selectMethodSymbol
          case (None, Some(_)) => selectMethodSymbol
          case (None, None) =>
            val prefixTPType = prefix.tpe.asRefType
            val replacedType = toRefType(accessor.tpe)
            lookupImplMethod(prefixTPType, replacedType, hargs, targs, argSummary.terms.map(_.tpe), methodName, requireStatic = false)
        }

        val pkg = referredMethodSymbol.path.pkgName
        val name = referredMethodSymbol.name
        val args = argSummary.terms.map(_.tpe.symbol).map(SigArg.Sym.apply)
        val signature = FunctionSignature(pkg, name, Some(accessor.tpe.symbol), args: _*)
        lazy val builtInFunction = builtinFunctions.find(_ == signature)
        lazy val isMemRead = prefix.tpe.asRefType.origin == Symbol.mem && methodName == "read"
        lazy val isMemWrite = prefix.tpe.asRefType.origin == Symbol.mem && methodName == "write"

        /*
        lazy val forBuiltin = forBuiltInMethod(_, Some(accessor), hargs, retTpe)
        val (call, label) = () match {
          case _ if isBuiltin => (forBuiltin(referredMethodSymbol), None)
          case _ if isMemRead => (backend.ReadMemory(accessor, argSummary.terms.head, retTpe), None)
          case _ if isMemWrite => (backend.WriteMemory(accessor, argSummary.terms(0), argSummary.terms(1)), None)
          case _ =>
            val label = makeLabel(referredMethodSymbol, Some(accessor.tpe), argSummary.terms.map(_.tpe), hargs, targs)
            val call = select.symbol match {
              case _: Symbol.MethodSymbol if isInterface => backend.CallInterface(label, accessor, argSummary.terms, retTpe)
              case _: Symbol.MethodSymbol => backend.CallMethod(label, Some(accessor), hargs, argSummary.terms, retTpe)
            }

            (call, Some(label))
        }
        */

        lazy val readMem = backend.ReadMemory(accessor, argSummary.terms.head, retTpe)
        lazy val writeMem = backend.WriteMemory(accessor, argSummary.terms(0), argSummary.terms(1))
        def builtin(sig: FunctionSignature) = backend.CallBuiltIn(sig.toString, Some(accessor.tpe), accessor +: argSummary.terms, hargs, retTpe)

        val (call, label) = builtInFunction match {
          case Some(_) if isMemRead => (readMem, None)
          case Some(_) if isMemWrite => (writeMem, None)
          case Some(function) => (builtin(function), None)
          case _ =>
            val label = makeLabel(referredMethodSymbol, Some(accessor.tpe), argSummary.terms.map(_.tpe), hargs, targs)
            val call = select.symbol match {
              case _: Symbol.MethodSymbol if isInterface => backend.CallInterface(label, accessor, argSummary.terms, retTpe)
              case _: Symbol.MethodSymbol => backend.CallMethod(label, Some(accessor), hargs, argSummary.terms, retTpe)
            }

            (call, Some(label))
        }

        val resultLabels = label.map(argSummary.labels ++ labels + _).getOrElse(argSummary.labels ++ labels)

        BuildResult((nodes :+ accessorNode) ++ argSummary.nodes, Some(call), resultLabels)
    }
  }

  def buildBinOp(binop: frontend.StdBinOp)(implicit ctx: BackendContext, global: GlobalData): BuildResult = {
    def toName(symbol: Symbol.ClassTypeSymbol): String = symbol match {
      case symbol if symbol == Symbol.int => "int"
      case symbol if symbol == Symbol.num => "num"
      case symbol if symbol == Symbol.bit => "bit"
      case symbol if symbol == Symbol.bool => "bool"
    }

    def methodName(tpe: String, ops: String): String = s"_builtin_${ops}_$tpe"

    def binOp(ops: String, symbols: Symbol.ClassTypeSymbol*): Vector[(Vector[Symbol.TypeSymbol], String)] = {
      val names = symbols.map(toName)

      (names zip symbols)
        .map { case (name, symbol) => Vector(symbol, symbol) -> methodName(name, ops) }
        .toVector
    }

    val int = Symbol.int
    val num = Symbol.num
    val bit = Symbol.bit
    val bool = Symbol.bool

    /*
    val builtInPairs = Map[frontend.Operation, Vector[(Vector[Symbol.TypeSymbol], String)]](
      frontend.Operation.Add -> binOp("add", int, num, bit),
      frontend.Operation.Sub -> binOp("sub", int, num, bit),
      frontend.Operation.Mul -> binOp("mul", int, num, bit),
      frontend.Operation.Div -> binOp("div", int, num, bit),
      frontend.Operation.Eq -> binOp("eq", int, num, bit, bool),
      frontend.Operation.Ne -> binOp("ne", int, num, bit, bool),
      frontend.Operation.Gt -> binOp("gt", int, num, bit),
      frontend.Operation.Ge -> binOp("ge", int, num, bit),
      frontend.Operation.Lt -> binOp("lt", int, num, bit),
      frontend.Operation.Le -> binOp("le", int, num, bit),
    )
    */

    val BuildResult(leftNodes, Some(leftExpr), leftLabels) = buildExpr(binop.left)
    val BuildResult(rightNodes, Some(rightExpr), rightLabels) = buildExpr(binop.right)
    val leftNode = backend.Temp(ctx.temp.get(), leftExpr)
    val rightNode = backend.Temp(ctx.temp.get(), rightExpr)
    val nodes = (leftNodes :+ leftNode) ++ (rightNodes :+ rightNode)
    val left = backend.Term.Temp(leftNode.id, leftExpr.tpe)
    val right = backend.Term.Temp(rightNode.id, rightExpr.tpe)

    def buildCallMethod(retTpe: BackendType): backend.CallMethod = {
      val leftTpe = toRefType(leftExpr.tpe)
      val rightTpe = toRefType(rightExpr.tpe)

      val (operator, _) = leftTpe.lookupOperator(binop.op, Some(rightTpe), Vector.empty, Vector.empty)
        .toEither
        .getOrElse(throw new ImplementationErrorException(s"operator[${binop.op}] for [$leftTpe] and [$rightTpe] should be found"))

      val targetMethod = operator.tpe.asMethodType
      val targetMethodTpe = targetMethod.params
      val callerTpe = Vector(leftExpr.tpe, rightExpr.tpe)
      val tpTable = buildTPTable(operator.tps, callerTpe, targetMethodTpe)

      val label = makeLabel(operator, None, Vector(leftExpr.tpe, rightExpr.tpe), Vector.empty, tpTable.values.toVector)

      backend.CallMethod(label, None, Vector.empty, Vector(left, right), retTpe)
    }

    val pkg = binop.symbol.path.pkgName
    val name = binop.symbol.name

    val function = FunctionSignature(pkg, name, None, SigArg.Sym(leftExpr.tpe.symbol), SigArg.Sym(rightExpr.tpe.symbol))
    val isBuiltin = builtinFunctions.contains(function)
    val retTpe = toBackendType(binop.tpe.asRefType, ctx.hpTable, ctx.tpTable)

    val call =
      if(isBuiltin) backend.CallBuiltIn(function.toString, None, Vector(left, right), Vector.empty, retTpe)
      else buildCallMethod(retTpe)

    /*
    val call = builtInPairs.get(binop.op) match {
      case None => buildCallMethod
      case Some(candidates) =>
        val leftTpeSymbol = leftExpr.tpe.symbol
        val rightTpeSymbol = rightExpr.tpe.symbol
        val called = candidates.find {
          case (Vector(left, right), _) => left == leftTpeSymbol && right == rightTpeSymbol
        }
        val retTpe = leftExpr.tpe

        called match {
          case None => buildCallMethod
          case Some((_, name)) => backend.CallBuiltIn(name, Vector(left, right), Vector.empty, retTpe)
        }
    }
    */

    val returnedLabels = call match {
      case call: backend.CallMethod => leftLabels ++ rightLabels + call.label
      case _: backend.CallBuiltIn => leftLabels ++ rightLabels
    }

    BuildResult(nodes, Some(call), returnedLabels)
  }

  def buildUnaryOp(unaryOp: frontend.StdUnaryOp)(implicit ctx: BackendContext, global: GlobalData): BuildResult = {
    def toName(symbol: Symbol.ClassTypeSymbol): String = symbol match {
      case symbol if symbol == Symbol.int => "int"
      case symbol if symbol == Symbol.num => "num"
      case symbol if symbol == Symbol.bit => "bit"
      case symbol if symbol == Symbol.bool => "bool"
    }

    def methodName(tpe: String, ops: String): String = s"__builtin_${tpe}_$ops"

    def unaryOps(ops: String, symbols: Symbol.ClassTypeSymbol*): Vector[(Symbol.ClassTypeSymbol, String)] = {
      val names = symbols.map(toName)

      (names zip symbols)
        .map { case (name, symbol) => symbol -> methodName(name, ops) }
        .toVector
    }

    val int = Symbol.int
    val num = Symbol.num
    val bit = Symbol.bit
    val bool = Symbol.bool

    val builtInPairs = Map[frontend.Operation, Vector[(Symbol.ClassTypeSymbol, String)]](
      frontend.Operation.Not -> unaryOps("not", int, num, bit, bool),
      frontend.Operation.Neg -> unaryOps("not", int, num, bit),
    )

    val BuildResult(operandNodes, Some(operandExpr), operandLabels) = buildExpr(unaryOp.operand)
    val opNode = backend.Temp(ctx.temp.get(), operandExpr)
    val operandStmts = operandNodes :+ opNode
    val operand = backend.Term.Temp(opNode.id, operandExpr.tpe)

    def buildCallMethod: backend.CallMethod = {
      val operandTpe = toRefType(operandExpr.tpe)
      val (operator, _) = operandTpe.lookupOperator(unaryOp.op, None, Vector.empty, Vector.empty)
        .toEither
        .getOrElse(throw new ImplementationErrorException(s"operator[${unaryOp.op}] for [$operandTpe] should be found"))

      val targetMethod = operator.tpe.asMethodType
      val targetMethodTpe = targetMethod.params
      val callerTpe = Vector(operand.tpe)
      val tpTable = buildTPTable(operator.tps, callerTpe, targetMethodTpe)

      val label = makeLabel(operator, None, Vector(operand.tpe), Vector.empty, tpTable.values.toVector)
      val retTpe = toBackendType(unaryOp.tpe.asRefType, ctx.hpTable, ctx.tpTable)

      backend.CallMethod(label, None, Vector.empty, Vector(operand), retTpe)
    }

    val call = builtInPairs.get(unaryOp.op) match {
      case None => buildCallMethod
      case Some(candidates) =>
        val operandTpeSymbol = operandExpr.tpe.symbol
        val called = candidates.find { case (ops, _) => ops == operandTpeSymbol }
        val retTpe = operandExpr.tpe

        called match {
          case None => buildCallMethod
          case Some((_, name)) => backend.CallBuiltIn(name, None, Vector(operand), Vector.empty, retTpe)
        }
    }

    val returnedLabels = call match {
      case call: backend.CallMethod => operandLabels + call.label
      case _: backend.CallBuiltIn => operandLabels
    }

    BuildResult(operandStmts, Some(call), returnedLabels)
  }

  def makeLabel(
    method: Symbol.MethodSymbol,
    accessor: Option[BackendType],
    args: Vector[BackendType],
    hargs: Vector[HPElem],
    targs: Vector[BackendType]
  )(implicit global: GlobalData): MethodLabel = {
    val (implHPTable, implTPTable, interface) = findImplClassTree(method, global) orElse findImplInterfaceTree(method, global) match {
      case Some(implTree: frontend.ImplementClass) =>
        val access = accessor.get
        val impl = implTree.symbol.asImplementSymbol
        val hpTable = buildHPTable(impl.hps, access, implTree.target.tpe.asRefType)
        val tpTable = buildTPTable(impl.tps, access, implTree.target.tpe.asRefType)

        (hpTable, tpTable, None)
      case Some(implTree: frontend.ImplementInterface) =>
        val access = accessor.get
        val impl = implTree.symbol.asImplementSymbol
        val callerTpes = access +: args
        val targetTpes = implTree.target.tpe.asRefType +: method.tpe.asMethodType.params

        val hpTable = buildHPTable(impl.hps, callerTpes, targetTpes)
        val tpTable = buildTPTable(impl.tps, callerTpes, targetTpes)
        val interface = implTree.interface.tpe.asRefType
        val interfaceTpe = toBackendType(interface, hpTable, tpTable)

        (hpTable, tpTable, Some(interfaceTpe))
      case None => (ListMap.empty, ListMap.empty, None)
    }

    val hpTable = implHPTable ++ ListMap.from(method.hps zip hargs)
    val tpTable = implTPTable ++ ListMap.from(method.tps zip targs)

    MethodLabel(method, accessor, interface, hpTable, tpTable)
  }

  def buildBlk(blk: frontend.Block)(implicit ctx: BackendContext, global: GlobalData): BuildResult = {
    val elem = blk.elems.foldLeft(BuildResult(Vector.empty, None, Set.empty)) {
      case (result, elem) =>
        val BuildResult(nodes, None, labels) = buildBlockElem(elem)
        BuildResult(result.nodes ++ nodes, None, result.labels ++ labels)
    }

    val BuildResult(nodes, Some(expr), labels) = buildExpr(blk.last)

    BuildResult(elem.nodes ++ nodes, Some(expr), elem.labels ++ labels)
  }

  def buildConstructClass(construct: frontend.ConstructClass)(implicit ctx: BackendContext, global: GlobalData): BuildResult = {
    case class Summary(nodes: Vector[backend.Stmt], initPairs: Vector[(String, backend.Expr)], labels: Set[BackendLabel])

    val Summary(nodes, inits, labels) = construct.fields.foldLeft(Summary(Vector.empty, Vector.empty, Set.empty)) {
      case (tempSummary, frontend.ConstructPair(name, init)) =>
        val BuildResult(nodes, Some(expr), labels) = buildExpr(init)

        Summary(
          tempSummary.nodes ++ nodes,
          tempSummary.initPairs :+ (name, expr),
          tempSummary.labels ++ labels
        )
    }

    val refTpe = construct.target.tpe.asRefType
    val tpe = toBackendType(refTpe, ctx.hpTable, ctx.tpTable)
    val expr = backend.ConstructStruct(tpe, inits.toMap)

    BuildResult(nodes, Some(expr), labels)
  }

  def buildConstructModule(construct: frontend.ConstructModule, instanceName: Option[String])(implicit ctx: BackendContext, global: GlobalData): BuildResult = {
    case class Summary(nodes: Vector[backend.Stmt], inits: Map[String, backend.Expr], labels: Set[BackendLabel])

    def buildInitSection(pairs: Vector[frontend.ConstructPair]): Summary = {
      pairs.foldLeft(Summary(Vector.empty, Map.empty, Set.empty)) {
        case (tempSummary, frontend.ConstructPair(name, init)) =>
          val BuildResult(nodes, Some(expr), labels) = buildExpr(init)

          Summary(
            tempSummary.nodes ++ nodes,
            tempSummary.inits + (name -> expr),
            tempSummary.labels ++ labels
          )
      }
    }

    val refTpe = construct.target.tpe.asRefType
    val tpe = toBackendType(refTpe, ctx.hpTable, ctx.tpTable)

    val parent = buildInitSection(construct.parents)
    val sibling = buildInitSection(construct.siblings)

    val nodes = parent.nodes ++ sibling.nodes
    val name = instanceName
      .map(backend.Term.Variable(_, tpe))
      .getOrElse(backend.Term.Temp(ctx.temp.get(), tpe))

    val expr =
      if(tpe.symbol == Symbol.mem) backend.ConstructMemory(name, tpe)
      else backend.ConstructModule(name, tpe, parent.inits, sibling.inits)

    val labels = parent.labels ++ sibling.labels

    BuildResult(nodes, Some(expr), labels)
  }

  def buildConstructEnum(enum: frontend.ConstructEnum)(implicit ctx: BackendContext, global: GlobalData): BuildResult = {
    val tpe = toBackendType(enum.tpe.asRefType, ctx.hpTable, ctx.tpTable)
    val fields = enum.fields.map(buildExpr)
    val (nodess, terms, labelss) = fields.map {
      case BuildResult(nodes, Some(expr), labels) =>
        val temp = backend.Temp(ctx.temp.get(), expr)
        (nodes :+ temp, backend.Term.Temp(temp.id, expr.tpe), labels)
    }.unzip3

    val construct = backend.ConstructEnum(tpe, enum.symbol.asEnumMemberSymbol, terms)

    BuildResult(nodess.flatten, Some(construct), labelss.flatten.toSet)
  }

  def buildIfExpr(ifExpr: frontend.IfExpr)(implicit ctx: BackendContext, global: GlobalData): BuildResult = {
    val BuildResult(condNodes, Some(condExpr), condLabels) = buildExpr(ifExpr.cond)
    val BuildResult(conseqNodes, Some(conseqExpr), conseqLabels) = buildExpr(ifExpr.conseq)
    val BuildResult(altNodes, altExpr, altLabels) = ifExpr.alt.map(buildExpr(_)(ctx, global)) match {
      case None => BuildResult(Vector.empty, None, Set.empty)
      case Some(result) => result
    }

    val condLastNode = backend.Temp(ctx.temp.get(), condExpr)
    val unitTpe = toBackendType(Type.unitTpe, Map.empty, Map.empty)

    val expr = backend.IfExpr(
      backend.Term.Temp(condLastNode.id, condExpr.tpe),
      conseqNodes,
      conseqExpr,
      altNodes,
      altExpr.getOrElse(backend.UnitLiteral()),
      altExpr.map(_.tpe).getOrElse(unitTpe)
    )

    BuildResult(condNodes, Some(expr), condLabels ++ conseqLabels ++ altLabels)
  }

  def buildMatch(matchExpr: frontend.Match)(implicit ctx: BackendContext, global: GlobalData): BuildResult = {
    def makeTemp(tpe: Type.RefType): backend.Term.Temp =
      backend.Term.Temp(ctx.temp.get(), toBackendType(tpe, ctx.hpTable, ctx.tpTable))

    def buildPatternMatching(pattern: frontend.MatchPattern): backend.MatchPattern = pattern match {
      case frontend.IdentPattern(ident) =>
        val name = ctx.label.toString + "$" + ident.symbol.path.innerPath.mkString("$")
        ctx.append(ident.symbol.asTermSymbol, name)

        val tpe = toBackendType(ident.tpe.asRefType, ctx.hpTable, ctx.tpTable)
        val variable = backend.Term.Variable(name, tpe)
        backend.IdentPattern(variable)
      case frontend.LiteralPattern(frontend.IntLiteral(value)) => backend.LiteralPattern(backend.IntLiteral(value))
      case frontend.LiteralPattern(frontend.BoolLiteral(value)) => backend.LiteralPattern(backend.BoolLiteral(value))
      case frontend.LiteralPattern(frontend.BitLiteral(value, width)) => backend.LiteralPattern(backend.BitLiteral(value, HPElem.Num(width)))
      case frontend.LiteralPattern(frontend.UnitLiteral()) => backend.LiteralPattern(backend.UnitLiteral())
      case frontend.LiteralPattern(frontend.StringLiteral(_)) => throw new ImplementationErrorException("string literal pattern does not implemented yet")
      case wild: frontend.WildCardPattern =>
        val tpe = toBackendType(wild.tpe.asRefType, ctx.hpTable, ctx.tpTable)
        backend.WildCardPattern(tpe)
      case frontend.EnumPattern(variant, patterns) =>
        val tpe = toBackendType(variant.tpe.asRefType, ctx.hpTable, ctx.tpTable)
        val allVariants = variant.tpe.declares.toMap
          .values.toVector
          .sortWith{ case (left, right) => left.name < right.name }

        val conds = patterns.map(buildPatternMatching)
        val idx = allVariants.indexOf(variant.symbol) match {
          case -1 => throw new ImplementationErrorException(s"${variant.symbol} cannot find from $allVariants")
          case idx => idx
        }

        backend.EnumPattern(idx, conds, tpe)
    }

    def buildCase(caseDef: frontend.Case): (backend.Case, Set[BackendLabel]) = {
      val pattern = buildPatternMatching(caseDef.pattern)
      val (stmtss, labelss) = caseDef.exprs
        .map(buildBlockElem)
        .map{
          case BuildResult(stmts, None, labels) => (stmts, labels)
          case BuildResult(stmts, Some(expr), labels) => (stmts :+ backend.Abandon(expr), labels)
        }
        .unzip

      val builtStmts = stmtss.flatten
      val stmts = builtStmts.init
      val backend.Abandon(expr) = builtStmts.last
      val labels = labelss.flatten.toSet
      val caseTree = backend.Case(pattern, stmts, expr)

      (caseTree, labels)
    }

    val BuildResult(exprStmts, Some(expr), labels) = buildExpr(matchExpr.expr)
    val retTpe = toBackendType(matchExpr.tpe.asRefType, ctx.hpTable, ctx.tpTable)
    val matchedTerm = backend.Temp(ctx.temp.get(), expr)
    val term = backend.Term.Temp(matchedTerm.id, matchedTerm.expr.tpe)

    val (cases, labelss) = matchExpr.cases.map(buildCase).unzip

    val backendMatch = backend.Match(term, cases, retTpe)

    BuildResult(exprStmts :+ matchedTerm, Some(backendMatch), labelss.flatten.toSet ++ labels)
  }

  def buildThis(ths: frontend.This)(implicit ctx: BackendContext, global: GlobalData): BuildResult = {
    val tpe = toBackendType(ths.tpe.asRefType, ctx.hpTable, ctx.tpTable)
    val expr = backend.This(tpe)

    BuildResult(Vector.empty, Some(expr), Set.empty)
  }

  def buildFinish(implicit ctx: BackendContext, global: GlobalData): BuildResult =
    finishPart

  def buildGenerate(generate: frontend.Generate)(implicit ctx: BackendContext, global: GlobalData): BuildResult =
    generatePart(generate.args, generate.symbol.asStageSymbol, generate.state)


  def buildGoto(goto: frontend.Goto)(implicit ctx: BackendContext, global: GlobalData): BuildResult = {
    val stateLabel = ctx.label.asInstanceOf[StateLabel]
    val stage = stateLabel.stage.symbol
    val states = stage.tpe.asMethodType
      .declares.toMap.values
      .collect { case state: Symbol.StateSymbol => state }
      .toVector
      .sortWith { case (left, right) => left.name < right.name }

    val targetStateIdx = states.indexOf(goto.symbol) match {
      case -1 => throw new ImplementationErrorException(s"${goto.symbol} does not exist in states")
      case index => index
    }

    val targetLabel = StateLabel(
      goto.symbol.asStateSymbol,
      ctx.label.accessor,
      stateLabel.stage,
      targetStateIdx,
      ctx.hpTable,
      ctx.tpTable
    )

    val argResults = goto.args.map(buildExpr)
    val argStmts = argResults.flatMap(_.nodes)
    val argTemps = argResults.map(_.last.get).map(backend.Temp(ctx.temp.get(), _))
    val argTerms = argTemps.map(temp => backend.Term.Temp(temp.id, temp.expr.tpe))
    val argLabels = argResults.flatMap(_.labels).toSet

    val target = backend.State(targetLabel, argTerms)

    val gotoExpr = backend.Goto(target)
    BuildResult(argStmts ++ argTemps, Some(gotoExpr), argLabels)
  }

  def buildRelay(relay: frontend.Relay)(implicit ctx: BackendContext, global: GlobalData): BuildResult = {
    val BuildResult(_, Some(finish), _) = finishPart
    val BuildResult(stmts, generate, labels) = generatePart(relay.params, relay.symbol.asStageSymbol, relay.state)
    val abandonFinish = backend.Abandon(finish)

    BuildResult(stmts :+ abandonFinish, generate, labels)
  }

  def buildReturn(ret: frontend.Return)(implicit ctx: BackendContext, global: GlobalData): BuildResult = {
    val stageLabel = ctx.label match {
      case stage: StageLabel => stage
      case state: StateLabel => state.stage
    }

    val BuildResult(stmts, Some(expr), labels) = buildExpr(ret.expr)
    val retStmt = backend.Abandon(backend.Return(stageLabel, expr))

    BuildResult(stmts :+ retStmt, Some(backend.UnitLiteral()), labels)
  }

  def finishPart(implicit ctx: BackendContext, global: GlobalData): BuildResult = {
    val stage = ctx.label match {
      case label: StageLabel => label
      case state: StateLabel => state.stage
    }

    BuildResult(Vector.empty, Some(backend.Finish(stage)), Set.empty)
  }

  def generatePart(args: Vector[frontend.Expression], target: Symbol.StageSymbol, stateInfo: Option[frontend.StateInfo])(implicit ctx: BackendContext, global: GlobalData): BuildResult = {
    val argResults = args.map(buildExpr(_)(ctx, global))

    val argStmts = argResults.flatMap(_.nodes)
    val argLabels = argResults.flatMap(_.labels).toSet

    val argExprs = argResults.map(_.last.get)
    val argPassedTemps = argExprs.map(expr => backend.Temp(ctx.temp.get(), expr))
    val argPassedTerms = (argExprs zip argPassedTemps).map {
      case (expr, temp) => backend.Term.Temp(temp.id, expr.tpe)
    }

    val states = target.tpe.asMethodType
      .declares.toMap
      .values
      .collect { case state: Symbol.StateSymbol => state }
      .toVector
      .sortWith { case (left, right) => left.name < right.name }

    val stageLabel = StageLabel(target, ctx.label.accessor, ctx.label.hps, ctx.label.tps)

    val (stateResult, state) = stateInfo match {
      case None => (BuildResult(Vector.empty, None, Set.empty), Option.empty)
      case Some(info) =>
        val gotIndex = states.indexOf(info.symbol)
        val index =
          if (gotIndex != -1) gotIndex
          else throw new ImplementationErrorException(s"${info.symbol} does not found in states")

        val argResults = info.args.map(buildExpr)
        val argLabels = argResults.flatMap(_.labels).toSet
        val argStmts = argResults.flatMap(_.nodes)
        val argTemps = argResults
          .flatMap(_.last)
          .map(expr => backend.Temp(ctx.temp.get(), expr))
        val argTerms = argTemps.map(temp => backend.Term.Temp(temp.id, temp.expr.tpe))

        val result = BuildResult(argStmts ++ argTemps, None, argLabels)
        val label = StateLabel(
          info.symbol.asStateSymbol,
          ctx.label.accessor,
          stageLabel,
          index,
          ctx.label.hps,
          ctx.label.tps
        )

        val state = backend.State(label, argTerms)

        (result, Some(state))
    }

    val retRefTpe = target.tpe.asMethodType.returnType
    val retTpe = toBackendType(retRefTpe, ctx.hpTable, ctx.tpTable)
    val generate = backend.Generate(stageLabel, argPassedTerms, state, retTpe)

    val stmts = argStmts ++ argPassedTemps ++ stateResult.nodes
    val labels = (argLabels + stageLabel) ++ stateResult.labels

    BuildResult(stmts, Some(generate), labels)
  }

  def buildBlockElem(elem: frontend.BlockElem)(implicit ctx: BackendContext, global: GlobalData): BuildResult =
    elem match {
      case expr: frontend.Expression =>
        val BuildResult(nodes, Some(last), labels) = buildExpr(expr)
        val lastNode = backend.Abandon(last)

        BuildResult(nodes :+ lastNode, None, labels)
      case vdef: frontend.ValDef =>
        val name = ctx.label.toString + "$" + vdef.symbol.path.innerPath.mkString("$")
        ctx.append(vdef.symbol.asTermSymbol, name)

        val refTpe = vdef.symbol.tpe.asRefType
        val tpe = toBackendType(refTpe, ctx.hpTable, ctx.tpTable)

        val BuildResult(stmts, Some(last), labels) = buildExpr(vdef.expr
          .getOrElse(throw new ImplementationErrorException("method's variable definition should have initialization expression"))
        )

        val v = backend.Variable(name, tpe, last)

        BuildResult(stmts :+ v, None, labels)
      case assign: frontend.Assign =>
        def buildLoc(expr: frontend.Expression): Vector[String] = expr match {
          case frontend.Select(prefix, name) => buildLoc(prefix) :+ name
          case frontend.This() => Vector.empty
        }

        val BuildResult(stmts, Some(expr), labels) = buildExpr(assign.right)
        val backendAssign = backend.Assign(buildLoc(assign.left), expr)

        BuildResult(stmts :+ backendAssign, None, labels)
    }

  trait SigArg
  object SigArg {
    case class Sym(symbol: Symbol.TypeSymbol) extends SigArg
    case object Any extends SigArg
  }
  case class FunctionSignature(pkg: Vector[String], name: String, accessor: Option[Symbol.TypeSymbol], args: SigArg*) {
    override def hashCode(): Int = pkg.hashCode + name.hashCode + accessor.hashCode + args.hashCode
    override def toString: String = {
      val accessor = this.accessor match {
        case None => ""
        case Some(symbol) => "_" + symbol.name.toLowerCase
      }

      val args = this.args.map {
        case SigArg.Sym(symbol) => "_" + symbol.name.toLowerCase
        case SigArg.Any => "_*"
      }

      s"$name$accessor${args.mkString("")}"
    }

    override def equals(obj: Any): Boolean = obj match {
      case sig: FunctionSignature =>
        lazy val samePkg = this.pkg == sig.pkg
        lazy val sameName = this.name == sig.name
        lazy val sameAccessor = this.accessor == sig.accessor
        lazy val sameArgLength = this.args.length == sig.args.length
        lazy val sameArg = (this.args zip sig.args).forall {
          case (SigArg.Any, _) => true
          case (_, SigArg.Any) => true
          case (SigArg.Sym(s0), SigArg.Sym(s1)) => s0 == s1
        }

        samePkg && sameName && sameAccessor && sameArgLength && sameArg
    }
  }

  def builtinFunctions(implicit global: GlobalData): Vector[FunctionSignature] = {
    val types = Vector("std", "types")
    val traits = Vector("std", "traits")
    val functions = Vector("std", "functions")

    val bit = Symbol.bit
    val int = Symbol.int
    val bool = Symbol.bool
    val vec = Symbol.vec
    val mem = Symbol.mem

    def makeFunctions(name: String, tpes: Symbol.TypeSymbol*): Vector[FunctionSignature] =
      tpes.map(symbol => FunctionSignature(functions, name, None, SigArg.Sym(symbol), SigArg.Sym(symbol))).toVector

    val adds = makeFunctions("add", int, bit)
    val subs = makeFunctions("sub", int, bit)
    val muls = makeFunctions("mul", int, bit)
    val divs = makeFunctions("div", int, bit)
    val eqns = makeFunctions("equal", int, bit, bool)
    val neqs = makeFunctions("notEqual", int, bit, bool)
    val ges  = makeFunctions("greaterEqual", int, bit)
    val gts  = makeFunctions("greaterThan", int, bit)
    val les  = makeFunctions("lessEqual", int, bit)
    val lts  = makeFunctions("lessThan", int, bit)
    val negs = makeFunctions("neg", int, bit)
    val nots = makeFunctions("not", int, bit, bool)
    val truncate = FunctionSignature(types, "truncate", Some(bit))
    val bitMethod = FunctionSignature(types, "bit", Some(bit))
    val concat = FunctionSignature(types, "concat", Some(bit), SigArg.Sym(bit))
    val idx = FunctionSignature(types, "idx", Some(vec))
    val idxDyn = FunctionSignature(types, "idxDyn", Some(vec), SigArg.Sym(bit))
    val updated = FunctionSignature(types, "updated", Some(vec), SigArg.Any)
    val updatedDyn = FunctionSignature(types, "updatedDyn", Some(vec), SigArg.Sym(bit), SigArg.Any)
    val read = FunctionSignature(types, "read", Some(mem), SigArg.Sym(bit))
    val write = FunctionSignature(types, "write", Some(mem), SigArg.Sym(bit), SigArg.Any)
    val bitFroms = Vector(bit, int, bool).map(symbol => FunctionSignature(traits, "from", Some(bit), SigArg.Sym(symbol)))

    val builtIns0 = Vector(
      adds, subs, muls, divs,
      eqns, neqs, ges, gts, les, lts,
      negs, nots, bitFroms
    ).flatten

    val builtIns1 = Vector(
      truncate, bitMethod, concat,
      idx, idxDyn, updated, updatedDyn,
      read, write,
    )

    builtIns0 ++ builtIns1
  }
}

abstract class BuildResult {
  val nodes: Vector[backend.Stmt]
  val last: Option[backend.Expr]
  val labels: Set[BackendLabel]
}

object BuildResult {
  def apply(nodes: Vector[backend.Stmt], last: Option[backend.Expr], labels: Set[BackendLabel]): BuildResult = {
    val _nodes = nodes
    val _last = last
    val _labels = labels

    new BuildResult {
      override val nodes = _nodes
      override val last = _last
      override val labels = _labels
    }
  }

  def apply(last: backend.Expr): BuildResult = {
    val _last = last

    new BuildResult {
      override val nodes = Vector.empty
      override val last = Some(_last)
      override val labels = Set.empty
    }
  }

  def unapply(obj: Any): Option[(Vector[backend.Stmt], Option[backend.Expr], Set[BackendLabel])] =
    obj match {
      case result: BuildResult => Some(result.nodes, result.last, result.labels)
      case _ => None
    }
}
