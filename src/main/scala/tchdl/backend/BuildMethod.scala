package tchdl.backend

import tchdl.backend.{ast => backend}
import tchdl.{ast => frontend}
import tchdl.typecheck.Typer
import tchdl.util._
import tchdl.util.TchdlException.ImplementationErrorException

import scala.collection.immutable.ListMap


object BuildMethod {
  def exec(implicit global: GlobalData): Either[Error, Vector[ModuleContainer]] = {


    val topModuleTpe = global.topModule.getOrElse(throw new ImplementationErrorException("top module's type should be there"))

  }

  def buildModule(module: Type.RefType)(implicit ctx: BackendContext, global: GlobalData) = {
    def isValidBounds(hpBounds: Vector[HPBound], tpBounds: Vector[TPBound]): Boolean = {
      hpBounds.map(HPBound.verifyMeetBound(_, Vector.empty)).forall(_.isRight) &&
      tpBounds.map(TPBound.verifyMeetBound(_, Vector.empty, Vector.empty)).forall(_.isRight)
    }

    val result = module.origin.asModuleSymbol.impls.flatMap {
      impl =>
        val (initHPTable, initTPTable) = Type.RefType.buildTable(impl)

        val hpTable = Type.RefType.assignHPTable(
          initHPTable,
          Vector(module),
          Vector(impl.targetType)
        ).getOrElse(throw new ImplementationErrorException("all hardware parameter table values should be assigned"))

        val tpTable = Type.RefType.assignTPTable(
          initTPTable,
          Vector(module),
          Vector(impl.targetType)
        ).getOrElse(throw new ImplementationErrorException("all hardware parameter table values should be assigned"))

        val assignedHPBound = HPBound.swapBounds(impl.symbol.asImplementSymbol.hpBound, hpTable)
        val assignedTPBound = TPBound.swapBounds(impl.symbol.asImplementSymbol.tpBound, hpTable, tpTable)
        val simplifiedHPBound = HPBound.simplify(assignedHPBound).getOrElse(throw new ImplementationErrorException("simplification should be succeed"))

        if(isValidBounds(simplifiedHPBound, assignedTPBound))  Option(impl, hpTable, tpTable)
        else None
    }

    val context = BackendContext(Map.empty, Map.empty, Vector.empty, Vector.empty)
    result match {
      case Vector() => Left(Error.TopModuleHasNoImpl(module))
      case Vector((impl, hpTable, tpTable)) =>
        val labelHPTable = hpTable.map{
          case (key, frontend.IntLiteral(value)) => key -> HPElem.Num(value)
          case (key, frontend.StringLiteral(value)) => key -> HPElem.Str(value)
        }.to(ListMap)

        val labelTPTable = tpTable.map {
          case (key, value) => key -> convertToBackendType(value, labelHPTable, Map.empty)
        }.to(ListMap)

        val implTree = findImplClassTree(impl.symbol.asImplementSymbol, global).getOrElse(throw new ImplementationErrorException("impl tree should be found"))

        val pairs = implTree.components
          .collect{ case mdef: frontend.MethodDef => mdef }
          .map(mdef => (mdef, MethodLabel(mdef.symbol.asMethodSymbol, labelHPTable, labelTPTable)))
          .map{ case (mdef, label) => label -> buildMethod(mdef, label)(context, global) }

        pairs.foreach {
          case (label, container) => context.methodTable(label) = Some(container)
        }

        implTree.components.foldLeft(ModuleContainer.empty(convertToBackendType(module, labelHPTable, labelTPTable))) {
          case (module, method: frontend.MethodDef) =>
            val label = MethodLabel(method.symbol.asMethodSymbol, labelHPTable, labelTPTable)
            val container = buildMethod(method, label)(context, global)

            module.addInterface(container)
          case (module, stage: frontend.StageDef) =>
            val label = StageLabel(stage.symbol.asStageSymbol, labelHPTable, labelTPTable)
            val container = buildStage(stage, label)(context, global)

            module.addStage(container)
          case (module, always: frontend.AlwaysDef) =>
            val (nodes, last) = buildBlk(always.blk)
            val code = nodes :+ last
            val container = AlwaysContainer(always.symbol.asAlwaysSymbol, code)

            module.addAlways(container)
          case (module, vdef: frontend.ValDef) =>
            val code = vdef.expr.map(buildExpr) match {
              case None => Vector.empty
              case Some((nodes, expr)) => nodes :+ backend.Return(expr)
            }
            val container = FieldContainer(vdef.flag, vdef.symbol.asVariableSymbol, code)

            module.addField(container)
        }
      case _ => throw new ImplementationErrorException("found multiple implementation")
    }
  }

  def buildMethod(methodDef: frontend.MethodDef, label: MethodLabel)(implicit ctx: BackendContext, global: GlobalData): MethodContainer = {
    val hargVariables = methodDef.hp.map { hp =>
      hp.symbol.tpe match {
        case tpe: Type.RefType if tpe =:= Type.numTpe =>
          val int = global.builtin.types.lookup("Int")
          val intTpe = BackendType(int, Vector.empty, Vector.empty)

          backend.Term.Variable(hp.symbol.path, intTpe)
        case tpe: Type.RefType if tpe =:= Type.strTpe =>
          val str = global.builtin.types.lookup("String")
          val strTpe = BackendType(str, Vector.empty, Vector.empty)

          backend.Term.Variable(hp.symbol.path, strTpe)
      }
    }

    val argVariables = methodDef.params.view.map(_.symbol).map {
      symbol =>
        val tpe = convertToBackendType(symbol.tpe.asRefType, label.hps, label.tps)
        val name = symbol.path

        backend.Term.Variable(name, tpe)
    }.to(Vector)

    val method = methodDef.symbol.asMethodSymbol
    val impl = findImplClassTree(method, global)
      .orElse(findImplInterfaceTree(method, global))
      .getOrElse(throw new ImplementationErrorException("method symbol should be found in implement"))
      .symbol.asImplementSymbol

    val blk = methodDef.blk.getOrElse(throw new ImplementationErrorException("impl's method should have body"))
    val hpBound = impl.hpBound ++ method.hpBound
    val tpBound = impl.tpBound ++ method.tpBound
    val thisMethodCtx = ctx.copy(label.hps, label.tps, hpBound, tpBound)
    val (nodes, expr) = buildExpr(blk)(thisMethodCtx, global)

    val asts = nodes :+ backend.Return(expr)
    MethodContainer(label, hargVariables, argVariables, asts)
  }

  def buildStage(stageDef: frontend.StageDef, label: StageLabel)(implicit ctx: BackendContext, global: GlobalData): StageContainer = {
    val blkElems = stageDef.blk.flatMap(buildBlockElem)
    val states = stageDef.states.map(buildState)
    val argVariables = stageDef.params.view.map(_.symbol).map {
      symbol =>
        val tpe = convertToBackendType(symbol.tpe.asRefType, label.hps, label.tps)
        val name = symbol.path

        backend.Term.Variable(name, tpe)
    }.to(Vector)

    StageContainer(label, argVariables, states, blkElems)
  }

  def buildState(stateDef: frontend.StateDef)(implicit ctx: BackendContext, global: GlobalData): StateContainer = {
    val (blk, last) = buildBlk(stateDef.blk)
    val code = blk :+ last

    StateContainer(stateDef.symbol.asStateSymbol, code)
  }

  def buildExpr(expr: frontend.Expression)(implicit ctx: BackendContext, global: GlobalData): (Vector[backend.BackendAST], backend.Expr) =
    expr match {
      case ident: frontend.Ident => buildIdent(ident)
      case select: frontend.Select => buildSelect(select)
      case apply: frontend.Apply => buildApply(apply)
      case binop: frontend.StdBinOp => buildBinOp(binop)
      case blk: frontend.Block => buildBlk(blk)
      case construct: frontend.ConstructClass => buildConstructClass(construct)
      case construct: frontend.ConstructModule => buildConstructModule(construct)
      case ifexpr: frontend.IfExpr => buildIfExpr(ifexpr)
      case finish: frontend.Finish => ???
      case goto: frontend.Goto => ???
      case generate: frontend.Generate => ???
      case relay: frontend.Relay => ???
      case frontend.IntLiteral(value) => (Vector.empty, backend.IntLiteral(value))
      case frontend.BitLiteral(value, length) => (Vector.empty, backend.BitLiteral(value, HPElem.Num(length)))
      case frontend.UnitLiteral() => (Vector.empty, backend.UnitLiteral())
      case frontend.StringLiteral(str) => (Vector.empty, backend.StringLiteral(str))
    }

  def buildSelect(select: frontend.Select)(implicit ctx: BackendContext, global: GlobalData): (Vector[backend.BackendAST], backend.Expr) = {
    val selectRefTpe = select.tpe.asRefType
    val selectTpe = convertToBackendType(selectRefTpe, ctx.hpTable, ctx.tpTable)

    select.prefix match {
      case frontend.This() => (Vector.empty, backend.ReferField(backend.Term.This, select.name, selectTpe))
      case expr =>
        val (nodes, last) = buildExpr(expr)
        val node = backend.Temp(ctx.temp.get(), last.tpe, last)
        val refer = backend.ReferField(backend.Term.Node(node.name, node.tpe), select.name, selectTpe)

        (nodes :+ node, refer)
    }
  }

  def buildIdent(ident: frontend.Ident)(implicit ctx: BackendContext, global: GlobalData): (Vector[backend.BackendAST], backend.Expr) = {
    val tpe = convertToBackendType(ident.tpe.asRefType, ctx.hpTable, ctx.tpTable)
    val term = backend.Term.Variable(ident.symbol.path, tpe)

    (Vector.empty, backend.Ident(term, tpe))
  }

  def buildApply(apply: frontend.Apply)(implicit ctx: BackendContext, global: GlobalData): (Vector[backend.BackendAST], backend.Expr) = {
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

      val (methodSymbol, methodTpe) = accessorTpe.lookupMethodFromBounds(argTpes, callerHP, callerTP, bounds, methodName)

      methodSymbol
    }

    def makeLabel(
      method: Symbol.MethodSymbol,
      hargs: Vector[HPElem],
      targs: Vector[BackendType]
    ): MethodLabel = {
      val hpTable = ListMap.newBuilder[Symbol.HardwareParamSymbol, HPElem]
        .addAll(method.hps zip hargs)
        .result()
      val tpTable = ListMap.newBuilder[Symbol.TypeParamSymbol, BackendType]
        .addAll(method.tps zip targs)
        .result()

      MethodLabel(method, hpTable, tpTable)
    }

    val (argExprs, argTerms) = apply.args.foldLeft((Vector.empty[backend.BackendAST], Vector.empty[backend.Term.Node])) {
      case ((temps, terms), arg) =>
        val (nodes, expr) = buildExpr(arg)
        val node = backend.Temp(ctx.temp.get(), expr.tpe, expr)

        val newTemps = temps ++ nodes :+ node
        val newTerms = terms :+ backend.Term.Node(node.name, node.tpe)
        (newTemps, newTerms)
    }

    val hargs = apply.hps.map(evalHPExpr(_, ctx.hpTable))
    val targs = apply.tps.view
      .map(_.tpe.asRefType)
      .map(convertToBackendType(_, ctx.hpTable, ctx.tpTable))
      .to(Vector)

    val (nodes, accessor, last, label) = apply.prefix match {
      case select @ frontend.Select(prefix, methodName) =>
        val (nodes, last) = buildExpr(prefix)
        val accessorNode = backend.Temp(ctx.temp.get(), last.tpe, last)
        val accessor = backend.Term.Node(accessorNode.name, accessorNode.tpe)
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
            lookupImplMethod(accessorTpe, hargs, targs, argTerms.map(_.tpe), methodName)
        }

        val label = makeLabel(referredMethodSymbol, hargs, targs)
        val call = select.symbol match {
          case _: Symbol.MethodSymbol if isInterface => backend.CallInterface(label, accessor, argTerms, retTpe)
          case _: Symbol.MethodSymbol => backend.CallMethod(label, Some(accessor), hargs, argTerms, retTpe)
        }

        ((nodes :+ accessorNode) ++ argExprs, accessor.tpe, call, label)
    }

    if (!ctx.methodTable.contains(label)) {
      ctx.methodTable += (label -> None)

      val isInterface =
        label.symbol.hasFlag(Modifier.Input) ||
          label.symbol.hasFlag(Modifier.Parent) ||
          label.symbol.hasFlag(Modifier.Sibling)

      if (isInterface)
        ctx.interfaceTable += (accessor -> label)
    }

    (nodes, last)
  }

  def buildBinOp(binop: frontend.StdBinOp)(implicit ctx: BackendContext, global: GlobalData): (Vector[backend.BackendAST], backend.Expr) = {
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

    val (leftNodes, leftExpr) = buildExpr(binop.left)
    val (rightNodes, rightExpr) = buildExpr(binop.right)
    val leftNode = backend.Temp(ctx.temp.get(), leftExpr.tpe, leftExpr)
    val rightNode = backend.Temp(ctx.temp.get(), rightExpr.tpe, rightExpr)
    val nodes = (leftNodes :+ leftNode) ++ (rightNodes :+ rightNode)
    val accessor = backend.Term.Node(leftNode.name, leftNode.tpe)
    val arg = backend.Term.Node(rightNode.name, rightNode.tpe)

    def buildCallMethod: backend.CallMethod = {
      val leftTpe = convertToRefType(leftNode.tpe)
      val rightTpe = convertToRefType(rightNode.tpe)

      val (operator, _) = leftTpe.lookupOperator(binop.op, rightTpe, Vector.empty, Vector.empty)
        .toEither
        .getOrElse(throw new ImplementationErrorException(s"operator[${binop.op}] for [$leftTpe] and [$rightTpe] should be found"))

      val emptyHPTable = ListMap.empty[Symbol.HardwareParamSymbol, HPElem]
      val emptyTPTable = ListMap.empty[Symbol.TypeParamSymbol, BackendType]
      val retTpe = convertToBackendType(binop.tpe.asRefType, ctx.hpTable, ctx.tpTable)

      val label = MethodLabel(operator, emptyHPTable, emptyTPTable)
      backend.CallMethod(label, Some(accessor), Vector.empty, Vector(arg), retTpe)
    }

    val call = builtInPairs.get(binop.op) match {
      case None => buildCallMethod
      case Some(candidates) =>
        val leftTpeSymbol = binop.left.tpe.asRefType.origin
        val rightTpeSymbol = binop.right.tpe.asRefType.origin
        val called = candidates.find {
          case (left, right, _) => left == leftTpeSymbol && right == rightTpeSymbol
        }
        val retTpe = leftNode.tpe

        called match {
          case None => buildCallMethod
          case Some((_, _, name)) => backend.CallBuiltIn(name, Vector(accessor, arg), retTpe)
        }
    }

    (nodes, call)
  }

  def buildBlk(blk: frontend.Block)(implicit ctx: BackendContext, global: GlobalData): (Vector[backend.BackendAST], backend.Expr) = {
    val asts = blk.elems.flatMap(buildBlockElem)
    val (nodes, expr) = buildExpr(blk.last)

    (asts ++ nodes, expr)
  }

  def buildConstructClass(construct: frontend.ConstructClass)(implicit ctx: BackendContext, global: GlobalData): (Vector[backend.BackendAST], backend.Expr) = {
    val (nodes, pairs) = construct.fields.foldLeft((Vector.empty[backend.BackendAST], Vector.empty[(String, backend.Expr)])) {
      case ((nodes, pairs), frontend.ConstructPair(name, init)) =>
        val (initNodes, initExpr) = buildExpr(init)

        (nodes ++ initNodes, pairs :+ (name, initExpr))
    }

    val refTpe = construct.target.tpe.asRefType
    val tpe = convertToBackendType(refTpe, ctx.hpTable, ctx.tpTable)
    val expr = backend.ConstructStruct(tpe, pairs.toMap)
    (nodes, expr)
  }

  def buildConstructModule(construct: frontend.ConstructModule)(implicit ctx: BackendContext, global: GlobalData): (Vector[backend.BackendAST], backend.Expr) = {
    def buildInitSection(pairs: Vector[frontend.ConstructPair]): (Vector[backend.BackendAST], Map[String, backend.Expr]) = {
      val (fieldNames, nodes, initExprs) = pairs
        .map { case frontend.ConstructPair(name, init) => name -> buildExpr(init) }
        .foldLeft((Vector.empty[String], Vector.empty[backend.BackendAST], Vector.empty[backend.Expr])) {
          case ((names, stackedNodes, exprs), (name, (nodes, expr))) =>
            (names :+ name, stackedNodes ++ nodes, exprs :+ expr)
        }

      val initPairs = (fieldNames zip initExprs).toMap
      (nodes, initPairs)
    }


    val refTpe = construct.target.tpe.asRefType
    val tpe = convertToBackendType(refTpe, ctx.hpTable, ctx.tpTable)

    val (parentNodes, parents) = buildInitSection(construct.parents)
    val (siblingNodes, siblings) = buildInitSection(construct.siblings)
    val nodes = parentNodes ++ siblingNodes

    val expr = backend.ConstructModule(tpe, parents, siblings)

    (nodes, expr)
  }

  def buildIfExpr(ifExpr: frontend.IfExpr)(implicit ctx: BackendContext, global: GlobalData): (Vector[backend.BackendAST], backend.IfExpr) = {
    val (condNodes, condExpr) = buildExpr(ifExpr.cond)
    val (conseqNodes, conseqExpr) = buildExpr(ifExpr.conseq)
    val (altNodes, altExpr) = ifExpr.alt.map(buildExpr) match {
      case None => (Vector.empty, backend.UnitLiteral())
      case Some(result) => result
    }

    val condLastNode = backend.Temp(ctx.temp.get(), condExpr.tpe, condExpr)
    val conseqLastNode = backend.Temp(ctx.temp.get(), condExpr.tpe, conseqExpr)
    val altLastNode = backend.Temp(ctx.temp.get(), condExpr.tpe, altExpr)
    val expr = backend.IfExpr(
      backend.Term.Node(condLastNode.name, condLastNode.tpe),
      conseqNodes :+ conseqLastNode,
      altNodes :+ altLastNode,
      altLastNode.tpe
    )

    (condNodes, expr)
  }

  def buildBlockElem(elem: frontend.BlockElem)(implicit ctx: BackendContext, global: GlobalData): Vector[backend.BackendAST] =
    elem match {
      case expr: frontend.Expression =>
        val (nodes, last) = buildExpr(expr)
        val lastNode = backend.Temp(ctx.temp.get(), last.tpe, last)
        nodes :+ lastNode
      case vdef: frontend.ValDef =>
        val refTpe = vdef.symbol.tpe.asRefType
        val tpe = convertToBackendType(refTpe, ctx.hpTable, ctx.tpTable)
        val v = backend.Variable(vdef.symbol.path, tpe)
        val (exprs, last) = buildExpr(vdef.expr.getOrElse(throw new ImplementationErrorException("method's variable definition should have initialization expression")))
        val assignTarget = backend.Term.Variable(vdef.symbol.path, last.tpe)
        val assign = backend.Assign(assignTarget, last)

        v +: exprs :+ assign
    }

  def evalHPExpr(hpExpr: frontend.HPExpr, hpTable: Map[Symbol.HardwareParamSymbol, HPElem]): HPElem =
    hpExpr match {
      case ident: frontend.Ident => hpTable.getOrElse(ident.symbol.asHardwareParamSymbol, throw new ImplementationErrorException("hardware parameter must be found"))
      case frontend.IntLiteral(value) => HPElem.Num(value)
      case frontend.StringLiteral(value) => HPElem.Str(value)
      case frontend.HPBinOp(op, left, right) =>
        val HPElem.Num(leftValue) = evalHPExpr(left, hpTable)
        val HPElem.Num(rightValue) = evalHPExpr(right, hpTable)

        op match {
          case frontend.Operation.Add => HPElem.Num(leftValue + rightValue)
          case frontend.Operation.Sub => HPElem.Num(leftValue - rightValue)
          case frontend.Operation.Mul => HPElem.Num(leftValue * rightValue)
          case frontend.Operation.Div => HPElem.Num(leftValue / rightValue)
        }
    }

  def findImplClassTree(impl: Symbol.ImplementSymbol, global: GlobalData): Option[frontend.ImplementClass] = {
    global.compilationUnits
      .filter(_.pkgName == impl.path.pkgName)
      .view
      .flatMap(_.topDefs)
      .collect { case impl: frontend.ImplementClass => impl }
      .find(_.symbol == impl)
  }

  def findImplClassTree(method: Symbol.MethodSymbol, global: GlobalData): Option[frontend.ImplementClass] = {
    global.compilationUnits
      .filter(_.pkgName == method.path.pkgName)
      .view
      .flatMap(_.topDefs)
      .collect { case impl: frontend.ImplementClass => impl }
      .find(_.components.exists(_.symbol == method))
  }

  def findImplInterfaceTree(method: Symbol.MethodSymbol, global: GlobalData): Option[frontend.ImplementInterface] = {
    global.compilationUnits
      .filter(_.pkgName == method.path.pkgName)
      .view
      .flatMap(_.topDefs)
      .collect { case impl: frontend.ImplementInterface => impl }
      .find(_.methods.exists(_.symbol == method))
  }

  def findMethodTree(method: Symbol.MethodSymbol, global: GlobalData): Option[frontend.MethodDef] = {
    global.compilationUnits
      .filter(_.pkgName == method.path.pkgName)
      .view
      .flatMap(_.topDefs)
      .collect {
        case impl: frontend.ImplementClass => impl.components
        case impl: frontend.ImplementInterface => impl.methods
      }
      .flatten
      .collect { case m: frontend.MethodDef => m }
      .find(_.symbol == method)
  }

  def convertToBackendType(
    tpe: Type.RefType,
    hpTable: Map[Symbol.HardwareParamSymbol, HPElem],
    tpTable: Map[Symbol.TypeParamSymbol, BackendType]
  ): BackendType = {
    def replace(tpe: Type.RefType): BackendType = tpe.origin match {
      case _: Symbol.EntityTypeSymbol =>
        val hargs = tpe.hardwareParam.map(evalHPExpr(_, hpTable))
        val targs = tpe.typeParam.map(replace)

        BackendType(tpe.origin, hargs, targs)
      case tp: Symbol.TypeParamSymbol =>
        tpTable.getOrElse(tp, throw new ImplementationErrorException(s"$tp should be found in tpTable"))
    }

    replace(tpe)
  }

  def convertToRefType(tpe: BackendType): Type.RefType = {
    def intoLiteral(elem: HPElem): frontend.HPExpr = elem match {
      case HPElem.Num(value) => frontend.IntLiteral(value)
      case HPElem.Str(value) => frontend.StringLiteral(value)
    }

    val hargs = tpe.hargs.map(intoLiteral)
    val targs = tpe.targs.map(convertToRefType)

    Type.RefType(tpe.symbol, hargs, targs)
  }
}
