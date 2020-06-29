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
    val (moduleContainers, labels) = modules.map(buildModule).unzip
    val labelSet = labels.flatten.toSet

    val initSummary = Summary(moduleContainers, Vector.empty, labelSet)
    val summary = build(initSummary)

    (summary.modules, summary.methods)
  }

  @tailrec def build(summary: Summary)(implicit global: GlobalData): Summary = {
    def isInterface(symbol: Symbol.MethodSymbol): Boolean =
      symbol.hasFlag(Modifier.Input) ||
        symbol.hasFlag(Modifier.Internal) ||
        symbol.hasFlag(Modifier.Parent) ||
        symbol.hasFlag(Modifier.Sibling)

    val interfaceContainers = summary.modules.flatMap(_.interfaces)
    val stageContainers = summary.modules.flatMap(_.stages)

    val unConstructedLabels = summary.labels.filterNot {
      case label: MethodLabel if isInterface(label.symbol) => interfaceContainers.exists(_.label == label)
      case label: MethodLabel => summary.methods.exists(_.label == label)
      case label: StageLabel => stageContainers.exists(_.label == label)
    }

    val renewedSummary = unConstructedLabels.foldLeft(summary) {
      case (summary, label: MethodLabel) if isInterface(label.symbol) =>
        val method = findMethodTree(label.symbol, global).getOrElse(throw new ImplementationErrorException("method tree should be found"))
        val context = BackendContext(label)
        val (container, labels) = buildMethod(method, label)(context, global)

        val modules = summary.modules.map {
          case module if module.tpe == label.accessor => module.addInterface(container)
          case module => module
        }

        Summary(modules, summary.methods, summary.labels ++ labels)
      case (summary, label: MethodLabel) =>
        val method = findMethodTree(label.symbol, global).getOrElse(throw new ImplementationErrorException("method tree should be found"))
        val context = BackendContext(label)
        val (container, labels) = buildMethod(method, label)(context, global)

        Summary(summary.modules, summary.methods :+ container, summary.labels ++ labels)
      case (summary, label: StageLabel) =>
        val stage = findStageTree(label.symbol, global).getOrElse(throw new ImplementationErrorException("stage tree should be found"))
        val context = BackendContext(label)
        val (container, labels) = buildStage(stage, label)(context, global)

        val modules = summary.modules.map {
          case module if module.tpe == label.accessor => module.addStage(container)
          case module => module
        }

        Summary(modules, summary.methods, summary.labels ++ labels)
    }

    if(unConstructedLabels.isEmpty) renewedSummary
    else build(renewedSummary)
  }

  def buildModule(builtModule: BuiltModule)(implicit global: GlobalData): (ModuleContainer, Set[BackendLabel]) = {
    val moduleContainer = ModuleContainer.empty(builtModule.module)

    builtModule.impl match {
      case None => (moduleContainer, Set.empty)
      case Some(impl) =>
        val hpTable = buildHPTable(impl.symbol.hps, builtModule.module, impl.targetType)
        val tpTable = buildTPTable(impl.symbol.tps, builtModule.module, impl.targetType)

        val implTree = findImplClassTree(impl.symbol.asImplementSymbol, global).getOrElse(throw new ImplementationErrorException("impl tree should be found"))

        val pairs = implTree.components.map {
          case method: frontend.MethodDef =>
            val label = MethodLabel(method.symbol.asMethodSymbol, moduleContainer.tpe, None, hpTable, tpTable)
            val context = BackendContext(label)
            val (container, labels) = buildMethod(method)(context, global)

            (container, labels)
          case stage: frontend.StageDef =>
            val label = StageLabel(stage.symbol.asStageSymbol, moduleContainer.tpe, hpTable, tpTable)
            val context = BackendContext(label)
            val (container, labels) = buildStage(stage)(context, global)

            (container, labels)
          case always: frontend.AlwaysDef =>
            val BuildResult(nodes, Some(last), labels) = buildBlk(always.blk)(context, global)
            val code = nodes :+ backend.Abandon(last)
            val container = AlwaysContainer(always.symbol.asAlwaysSymbol, code)

            (container, labels)
          case vdef: frontend.ValDef =>
            val exprResult= vdef.expr
              .map(buildExpr(_)(context, global))
              .getOrElse(BuildResult(Vector.empty, None, Set.empty))

            val tpe = convertToBackendType(vdef.symbol.tpe.asRefType, hpTable, tpTable)

            val container = FieldContainer(
              vdef.flag,
              vdef.symbol.asVariableSymbol,
              exprResult.nodes,
              exprResult.last,
              tpe
            )

            (container, exprResult.labels)
        }

        val (containers, labels) = pairs.unzip
        val labelSet = labels.flatten.toSet
        val assignedModule = containers.foldLeft(moduleContainer) {
          case (module, c: MethodContainer) => module.addInterface(c)
          case (module, c: StageContainer) => module.addStage(c)
          case (module, c: AlwaysContainer) => module.addAlways(c)
          case (module, c: FieldContainer) => module.addField(c)
        }

        (assignedModule, labelSet)
    }
  }

  def buildMethod(methodDef: frontend.MethodDef)(implicit ctx: BackendContext[MethodLabel], global: GlobalData): (MethodContainer, Set[BackendLabel]) = {
    val methodName = ctx.label.toString

    val hargNames = methodDef.hp.map(hp => methodName + "$" + hp.name)
    val hargTpes = methodDef.hp.view.map(_.symbol.tpe.asRefType).map(convertToBackendType(_, ctx.label.hps, ctx.label.tps))
    val hargs = ListMap.from(hargNames zip hargTpes)

    val argNames = methodDef.params.map(param => methodName + "$" + param.name)
    val argTpes = methodDef.params.map(_.symbol.tpe.asRefType).map(convertToBackendType(_, ctx.label.hps, ctx.label.tps))
    val args = ListMap.from(argNames zip argTpes)

    val blk = methodDef.blk.getOrElse(throw new ImplementationErrorException("impl's method should have body"))
    val BuildResult(nodes, Some(expr), labels) = buildExpr(blk)

    (MethodContainer(ctx.label, hargs, args, nodes, expr), labels)
  }

  def buildStage(stageDef: frontend.StageDef)(implicit ctx: BackendContext[StageLabel], global: GlobalData): (StageContainer, Set[BackendLabel]) = {
    val BuildResult(blkNodes, None, blkLabels) = stageDef.blk
      .map(buildBlockElem)
      .foldLeft(BuildResult(Vector.empty, None, Set.empty)) {
        case (summary, result) =>
          BuildResult(
            summary.nodes ++ result.nodes,
            None,
            summary.labels ++ result.labels
          )
      }

    val (states, stateLabels) = stageDef.states.map(buildState).unzip
    val argNames = stageDef.params.map(_.symbol.name)
    val argTpes = stageDef.params.view.map(_.symbol.tpe.asRefType).map(convertToBackendType(_, ctx.hpTable, ctx.tpTable))
    val args = ListMap.from(argNames zip argTpes)

    (StageContainer(ctx.label, args, states, blkNodes), blkLabels ++ stateLabels.flatten)
  }

  def buildState(stateDef: frontend.StateDef)(implicit ctx: BackendContext[StateLabel], global: GlobalData): (StateContainer, Set[BackendLabel]) = {
    val BuildResult(nodes, last, labels) = buildBlk(stateDef.blk)
    val lastStmt = last.map(backend.Abandon.apply).getOrElse(backend.Abandon(backend.UnitLiteral()))
    val code = nodes :+ lastStmt

    (StateContainer(stateDef.symbol.asStateSymbol, code), labels)
  }

  def buildExpr[T <: BackendLabel](expr: frontend.Expression)(implicit ctx: BackendContext[T], global: GlobalData): BuildResult =
    expr match {
      case ident: frontend.Ident => buildIdent(ident)
      case select: frontend.Select => buildSelect(select)
      case apply: frontend.Apply => buildApply(apply)
      case binop: frontend.StdBinOp => buildBinOp(binop)
      case blk: frontend.Block => buildBlk(blk)
      case construct: frontend.ConstructClass => buildConstructClass(construct)
      case construct: frontend.ConstructModule => buildConstructModule(construct)
      case ifexpr: frontend.IfExpr => buildIfExpr(ifexpr)
      case ths: frontend.This => buildThis(ths)
      case finish: frontend.Finish => ???
      case goto: frontend.Goto => ???
      case generate: frontend.Generate => ???
      case relay: frontend.Relay => ???
      case frontend.IntLiteral(value) => BuildResult(backend.IntLiteral(value))
      case frontend.BitLiteral(value, length) => BuildResult(backend.BitLiteral(value, HPElem.Num(length)))
      case frontend.UnitLiteral() => BuildResult(backend.UnitLiteral())
      case frontend.StringLiteral(str) => BuildResult(backend.StringLiteral(str))
    }

  def buildIdent(ident: frontend.Ident)(implicit ctx: BackendContext, global: GlobalData): BuildResult = {
    val tpe = convertToBackendType(ident.tpe.asRefType, ctx.hpTable, ctx.tpTable)
    val term = backend.Term.Variable(nameFromPath(ident.symbol.path), tpe)

    BuildResult(Vector.empty, Some(backend.Ident(term, tpe)), Set.empty)
  }

  def buildSelect(select: frontend.Select)(implicit ctx: BackendContext, global: GlobalData): BuildResult = {
    val selectRefTpe = select.tpe.asRefType
    val selectTpe = convertToBackendType(selectRefTpe, ctx.hpTable, ctx.tpTable)

    val BuildResult(nodes, Some(last), labels) = buildExpr(select.prefix)
    val node = backend.Temp(ctx.temp.get(), last)
    val refer = backend.ReferField(backend.Term.Temp(node.id, last.tpe), select.name, selectTpe)

    BuildResult(nodes :+ node, Some(refer), labels)
  }

  def buildApply(apply: frontend.Apply)(implicit ctx: BackendContext, global: GlobalData): BuildResult = {
    case class Summary(nodes: Vector[backend.Stmt], passeds: Vector[backend.Term.Temp], labels: Set[BackendLabel])

    def replaceTPBound(bound: TPBound): TPBound = {
      val replacedBounds = bound.bounds
        .map(convertToBackendType(_, ctx.hpTable, ctx.tpTable))
        .map(convertToRefType)

      TPBound(bound.target, replacedBounds)
    }

    def lookupImplMethod(
      accessorTpe: Type.RefType,
      hargs: Vector[HPElem],
      targs: Vector[BackendType],
      args: Vector[BackendType],
      methodName: String,
    ): Symbol.MethodSymbol = {
      val bounds = ctx.tpBounds.find(_.target =:= accessorTpe)
        .map(replaceTPBound)
        .map(_.bounds)
        .getOrElse(Vector.empty)

      val callerHP = hargs.map {
        case HPElem.Num(value) => frontend.IntLiteral(value)
        case HPElem.Str(value) => frontend.StringLiteral(value)
      }
      val callerTP = targs.map(convertToRefType)
      val argTpes = args.map(convertToRefType)

      val (methodSymbol, _) = accessorTpe.lookupMethodFromBounds(argTpes, callerHP, callerTP, bounds, methodName)

      methodSymbol
    }

    val argSummary = apply.args.foldLeft(Summary(Vector.empty, Vector.empty, Set.empty)) {
      case (summary, arg) =>
        val BuildResult(nodes, Some(expr), labels) = buildExpr(arg)
        val node = backend.Temp(ctx.temp.get(), expr)

        val newTemps = summary.nodes ++ nodes :+ node
        val newTerms = summary.passeds :+ backend.Term.Temp(node.id, expr.tpe)

        Summary(newTemps, newTerms, labels)
    }

    val hargs = apply.hps.map(evalHPExpr(_, ctx.hpTable))
    val targs = apply.tps.view
      .map(_.tpe.asRefType)
      .map(convertToBackendType(_, ctx.hpTable, ctx.tpTable))
      .toVector

    apply.prefix match {
      case select @ frontend.Select(prefix, methodName) =>
        val BuildResult(nodes, Some(last), labels) = buildExpr(prefix)
        val accessorNode = backend.Temp(ctx.temp.get(), last)
        val accessor = backend.Term.Temp(accessorNode.id, last.tpe)
        val isInterface =
          select.symbol.hasFlag(Modifier.Input) ||
          select.symbol.hasFlag(Modifier.Parent) ||
          select.symbol.hasFlag(Modifier.Sibling)

        val selectMethodSymbol = select.symbol.asMethodSymbol
        val retTpe = convertToBackendType(apply.tpe.asRefType, ctx.hpTable, ctx.tpTable)
        val referredMethodSymbol = (findImplClassTree(selectMethodSymbol, global), findImplInterfaceTree(selectMethodSymbol, global)) match {
          case (Some(_), _) => selectMethodSymbol
          case (None, Some(_)) => selectMethodSymbol
          case (None, None) =>
            val accessorTpe = convertToRefType(accessor.tpe)
            lookupImplMethod(accessorTpe, hargs, targs, argSummary.passeds.map(_.tpe), methodName)
        }

        val label = makeLabel(referredMethodSymbol, accessor.tpe, argSummary.passeds.map(_.tpe), hargs, targs)
        val call = select.symbol match {
          case _: Symbol.MethodSymbol if isInterface => backend.CallInterface(label, accessor, argSummary.passeds, retTpe)
          case _: Symbol.MethodSymbol => backend.CallMethod(label, Some(accessor), hargs, argSummary.passeds, retTpe)
        }

        BuildResult(
          (nodes :+ accessorNode) ++ argSummary.nodes,
          Some(call),
          argSummary.labels ++ labels + label
        )
    }
  }

  def buildBinOp(binop: frontend.StdBinOp)(implicit ctx: BackendContext, global: GlobalData): BuildResult = {
    val int = global.builtin.types.symbols.find(_.name == "Int").get
    val num = global.builtin.types.symbols.find(_.name == "Num").get
    val bit = global.builtin.types.symbols.find(_.name == "Bit").get

    val builtInPairs = Map[frontend.Operation, Vector[(Symbol.TypeSymbol, Symbol.TypeSymbol, String)]](
      frontend.Operation.Add -> Vector(
        (int, int, "_builtin_add_int_int"),
        (num, num, "_builtin_add_int_int"),
        (bit, bit, "_builtin_add_bit_bit"),
      ),
      frontend.Operation.Sub -> Vector(
        (int, int, "_builtin_sub_int_int"),
        (num, num, "_builtin_add_int_int"),
        (bit, bit, "_builtin_sub_bit_bit"),
      ),
      frontend.Operation.Mul -> Vector(
        (int, int, "_builtin_mul_int_int"),
        (num, num, "_builtin_add_int_int"),
        (bit, bit, "_builtin_mul_bit_bit"),
      ),
      frontend.Operation.Div -> Vector(
        (int, int, "_builtin_div_int_int"),
        (num, num, "_builtin_add_int_int"),
        (bit, bit, "_builtin_div_bit_bit"),
      ),
    )

    val BuildResult(leftNodes, Some(leftExpr), leftLabels) = buildExpr(binop.left)
    val BuildResult(rightNodes, Some(rightExpr), rightLabels) = buildExpr(binop.right)
    val leftNode = backend.Temp(ctx.temp.get(), leftExpr)
    val rightNode = backend.Temp(ctx.temp.get(), rightExpr)
    val nodes = (leftNodes :+ leftNode) ++ (rightNodes :+ rightNode)
    val accessor = backend.Term.Temp(leftNode.id, leftExpr.tpe)
    val arg = backend.Term.Temp(rightNode.id, rightExpr.tpe)

    def buildCallMethod: backend.CallMethod = {
      val leftTpe = convertToRefType(leftExpr.tpe)
      val rightTpe = convertToRefType(rightExpr.tpe)

      val (operator, _) = leftTpe.lookupOperator(binop.op, rightTpe, Vector.empty, Vector.empty)
        .toEither
        .getOrElse(throw new ImplementationErrorException(s"operator[${binop.op}] for [$leftTpe] and [$rightTpe] should be found"))

      val label = makeLabel(operator, leftExpr.tpe, Vector(rightExpr.tpe), Vector.empty, Vector.empty)
      val retTpe = convertToBackendType(binop.tpe.asRefType, ctx.hpTable, ctx.tpTable)

      backend.CallMethod(label, Some(accessor), Vector.empty, Vector(arg), retTpe)
    }

    val call = builtInPairs.get(binop.op) match {
      case None => buildCallMethod
      case Some(candidates) =>
        val leftTpeSymbol = leftExpr.tpe.symbol
        val rightTpeSymbol = rightExpr.tpe.symbol
        val called = candidates.find {
          case (left, right, _) => left == leftTpeSymbol && right == rightTpeSymbol
        }
        val retTpe = leftExpr.tpe

        called match {
          case None => buildCallMethod
          case Some((_, _, name)) => backend.CallBuiltIn(name, Vector(accessor, arg), retTpe)
        }
    }

    val returnedLabels = call match {
      case call: backend.CallMethod => leftLabels ++ rightLabels + call.label
      case _: backend.CallBuiltIn => leftLabels ++ rightLabels
    }

    BuildResult(nodes, Some(call), returnedLabels)
  }

  def makeLabel(
    method: Symbol.MethodSymbol,
    accessor: BackendType,
    args: Vector[BackendType],
    hargs: Vector[HPElem],
    targs: Vector[BackendType]
  )(implicit global: GlobalData): MethodLabel = {
    val (implHPTable, implTPTable, interface) = findImplClassTree(method, global) orElse findImplInterfaceTree(method, global) match {
      case Some(implTree: frontend.ImplementClass) =>
        val impl = implTree.symbol.asImplementSymbol
        val hpTable = buildHPTable(impl.hps, accessor, implTree.target.tpe.asRefType)
        val tpTable = buildTPTable(impl.tps, accessor, implTree.target.tpe.asRefType)

        (hpTable, tpTable, None)
      case Some(implTree: frontend.ImplementInterface) =>
        val impl = implTree.symbol.asImplementSymbol
        val callerTpes = accessor +: args
        val targetTpes = implTree.target.tpe.asRefType +: method.tpe.asMethodType.params

        val hpTable = buildHPTable(impl.hps, callerTpes, targetTpes)
        val tpTable = buildTPTable(impl.tps, callerTpes, targetTpes)
        val interface = implTree.interface.tpe.asRefType
        val interfaceTpe = convertToBackendType(interface, hpTable, tpTable)

        (hpTable, tpTable, Some(interfaceTpe))
    }

    val hpTable = implHPTable ++ ListMap.from(method.hps zip hargs)
    val tpTable = implTPTable ++ ListMap.from(method.tps zip targs)

    MethodLabel(method, accessor, interface, hpTable, tpTable)
  }

  def buildBlk(blk: frontend.Block)(implicit ctx: BackendContext, global: GlobalData): BuildResult = {
    val elem = blk.elems.foldLeft(BuildResult(Vector.empty, None, Set.empty)){
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
    val tpe = convertToBackendType(refTpe, ctx.hpTable, ctx.tpTable)
    val expr = backend.ConstructStruct(tpe, inits.toMap)

    BuildResult(nodes, Some(expr), labels)
  }

  def buildConstructModule(construct: frontend.ConstructModule)(implicit ctx: BackendContext, global: GlobalData): BuildResult = {
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
    val tpe = convertToBackendType(refTpe, ctx.hpTable, ctx.tpTable)

    val parent = buildInitSection(construct.parents)
    val sibling = buildInitSection(construct.siblings)

    val nodes = parent.nodes ++ sibling.nodes
    val expr = backend.ConstructModule(tpe, parent.inits, sibling.inits)
    val labels = parent.labels ++ sibling.labels

    BuildResult(nodes, Some(expr), labels)
  }

  def buildIfExpr(ifExpr: frontend.IfExpr)(implicit ctx: BackendContext, global: GlobalData): BuildResult = {
    val BuildResult(condNodes, Some(condExpr), condLabels) = buildExpr(ifExpr.cond)
    val BuildResult(conseqNodes, Some(conseqExpr), conseqLabels) = buildExpr(ifExpr.conseq)
    val BuildResult(altNodes, altExpr, altLabels) = ifExpr.alt.map(buildExpr) match {
      case None => BuildResult(Vector.empty, None, Set.empty)
      case Some(result) => result
    }

    val condLastNode = backend.Temp(ctx.temp.get(), condExpr)
    val unitTpe = convertToBackendType(Type.unitTpe, Map.empty, Map.empty)

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

  def buildThis(ths: frontend.This)(implicit ctx: BackendContext, global: GlobalData): BuildResult = {
    val tpe = convertToBackendType(ths.tpe.asRefType, ctx.hpTable, ctx.tpTable)
    val expr = backend.This(tpe)

    BuildResult(Vector.empty, Some(expr), Set.empty)
  }

  def buildBlockElem(elem: frontend.BlockElem)(implicit ctx: BackendContext, global: GlobalData): BuildResult =
    elem match {
      case expr: frontend.Expression =>
        val BuildResult(nodes, Some(last), labels) = buildExpr(expr)
        val lastNode = backend.Abandon(last)

        BuildResult(nodes :+ lastNode, None, labels)
      case vdef: frontend.ValDef =>
        val refTpe = vdef.symbol.tpe.asRefType
        val tpe = convertToBackendType(refTpe, ctx.hpTable, ctx.tpTable)

        val BuildResult(stmts, Some(last), labels) = buildExpr(vdef.expr
            .getOrElse(throw new ImplementationErrorException("method's variable definition should have initialization expression"))
        )

        val v = backend.Variable(nameFromPath(vdef.symbol.path), tpe, last)

        BuildResult(stmts :+ v, None, labels)
    }

  def nameFromPath(path: NameSpace)(implicit ctx: BackendContext): String =
    (path.path.tail :+ path.name.get).mkString("$")
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
