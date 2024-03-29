package tchdl.backend

import tchdl.backend.{ast => backend}
import tchdl.backend.ast.{BackendLIR => lir}
import tchdl.util._
import tchdl.util.TchdlException._
import firrtl.PrimOps

import scala.annotation.tailrec
import scala.collection.immutable.ListMap
import scala.collection.mutable

object BackendLIRGen {
  case class BuildResult[T](stmts: Vector[lir.Stmt], component: T)
  case class FirrtlContext(
    interfaces: Map[BackendType, Vector[MethodContainer]],
    stages: Map[BackendType, Vector[StageContainer]],
    procs: Map[BackendType, Vector[ProcContainer]],
    methods: Map[BackendType, Vector[MethodContainer]],
    inputs: Map[BackendType, Vector[FieldContainer]],
    functions: Vector[MethodContainer],
  )

  def exec(modules: Vector[ModuleContainer], methods: Vector[MethodContainer])(implicit global: GlobalData): Vector[lir.Module] = {
    val interfaceTable = modules.map(module => module.tpe -> module.bodies.flatMap(_.interfaces)).toMap
    val stageTable = modules.map(module => module.tpe -> module.bodies.flatMap(_.stages)).toMap
    val procTable = modules.map(module => module.tpe -> module.bodies.flatMap(_.procs)).toMap
    val methodTable = methods
      .collect { case method if method.label.accessor.isDefined => method }
      .groupBy(_.label.accessor.get)
    val inputs = modules
      .map(module => module.tpe -> module.bodies.flatMap(_.fields))
      .map{ case (tpe, fields) => tpe -> fields.filter(_.flag.hasFlag(Modifier.Input)) }
      .toMap

    val functionTable = methods.collect { case method if method.label.accessor.isEmpty => method }
    val context = FirrtlContext(
      interfaceTable,
      stageTable,
      procTable,
      methodTable,
      inputs,
      functionTable
    )

    modules.filter(_.isNeedElaborate).map(buildModule(_, context))
  }

  def buildModule(module: ModuleContainer, ctx: FirrtlContext)(implicit global: GlobalData): lir.Module = {
    val instance = ModuleInstance(module.tpe, ModuleLocation.This)
    val stack = StackFrame(instance)

    val modules = module.bodies.map(elaborate(_, module.tpe)(stack, ctx, global))
    val moduleField = global.lookupFields(module.tpe)
    val (upperPorts, upperPortInits) = moduleField
      .toVector
      .map { case (name, tpe) => buildUpperModule(name, tpe)(stack, ctx, global) }
      .unzip

    val elaborated = modules.reduceLeft[lir.Module] {
      case (acc, module) =>
        val ports = acc.ports ++ module.ports
        val mems = acc.mems ++ module.mems
        val instances = acc.subs ++ module.subs
        val components = acc.components ++ module.components
        val inits = acc.inits ++ module.inits
        val procedures = acc.procedures ++ module.procedures

        lir.Module(module.tpe, ports, instances, mems, components, inits, procedures)
    }

    val ports = elaborated.ports ++ upperPorts.flatten
    val inits = upperPortInits.flatten ++ elaborated.inits

    elaborated.copy(ports = ports, inits = inits)
  }

  def elaborate(module: ModuleContainerBody, tpe: BackendType)(implicit stack: StackFrame, ctx: FirrtlContext, global: GlobalData): lir.Module = {
    val hpStmts = module.hps.toVector
      .map { case (name, elem) => stack.next(name) -> elem }
      .flatMap {
        case (name, HPElem.Num(num)) =>
          val RunResult(intStmts, inst) = DataInstance.int(num)
          stack.append(name, inst)
          intStmts
        case (name, HPElem.Str(str)) =>
          stack.append(name, StringInstance(str))
          Vector.empty
      }

    // fields into stack
    module.fields.foreach { field =>
      val name = field.toFirrtlString
      stack.lock(name)
      val ref = lir.Reference(stack.refer(name).name, field.tpe)
      val instance =
        if(field.flag.hasFlag(Modifier.Child)) ModuleInstance(field.tpe, ModuleLocation.Sub(ref))
        else DataInstance(field.tpe, ref)

      stack.append(stack.refer(name), instance)
    }

    val inputs = module.fields
      .filter(_.flag.hasFlag(Modifier.Input))
      .map(runInput(_)(stack, ctx, global))

    val outputs = module.fields
      .filter(_.flag.hasFlag(Modifier.Output))
      .map(runOutput(_)(stack, ctx, global))

    val internals = module.fields
      .filter(_.flag.hasFlag(Modifier.Internal))
      .map(runInternal(_)(stack, ctx, global))

    val registers = module.fields
      .filter(_.flag.hasFlag(Modifier.Register))
      .map(runRegister(_)(stack, ctx, global))

    val modules = module.fields
      .filter(_.flag.hasFlag(Modifier.Child))
      .filter(_.tpe.symbol != Symbol.mem)
      .map(runSubModule(_)(stack, ctx, global))

    val memories = module.fields
      .filter(_.flag.hasFlag(Modifier.Child))
      .filter(_.tpe.symbol == Symbol.mem)
      .map(runMemory(_)(stack, ctx, global))


    val (inputInterContainers, normalInterContainers) = module.interfaces.partition{ interface =>
      val symbol = interface.label.symbol
      symbol.hasFlag(Modifier.Input) || symbol.hasFlag(Modifier.Sibling)
    }
    val inputInterfaces = inputInterContainers.map(buildInputInterfaceSignature(_)(stack, global))
    val normalInterfaces = normalInterContainers.map(buildInternalInterfaceSignature(_)(stack, global))
    val stageSigPairs = module.stages.map(buildStageSignature(_)(stack, ctx, global))
    val stageSigs = stageSigPairs.flatMap(_.stmts) ++ stageSigPairs.flatMap(_.component)
    val procSigss = module.procs.map(buildProcSignature(_)(stack, ctx, global))

    val ports = inputs.map(_.component) ++ outputs.map(_.component) ++ inputInterfaces.flatMap(_.component)
    val components = internals.map(_.component) ++ registers.flatMap(_.stmts) ++ registers.map(_.component) ++ normalInterfaces.flatMap(_.component) ++ stageSigs ++ procSigss.flatten
    val (instances, accessCondss) = modules.map(_.component).unzip
    val mems = memories.map(_.component)

    val interfaceInits = inputs.flatMap(_.stmts) ++ outputs.flatMap(_.stmts) ++ internals.flatMap(_.stmts)
    val componentInits = modules.flatMap(_.stmts) ++ memories.flatMap(_.stmts) ++ inputInterfaces.flatMap(_.stmts) ++ normalInterfaces.flatMap(_.stmts)

    val interfaceBodies = module.interfaces.map(runInterface(_)(stack, ctx, global))
    val alwayss = module.always.map(runAlways(_)(stack, ctx, global))
    val stageBodies = module.stages.map(runStage(_)(stack, ctx, global))
    val procBodies = module.procs.map(runProc(_)(stack, ctx, global))
    val procedures = accessCondss.flatten ++ interfaceBodies.map(_.component) ++ stageBodies.map(_.component) ++ procBodies.flatMap(_.component) ++ alwayss.flatMap(_.stmts)

    val inits = interfaceInits ++ componentInits ++ procBodies.flatMap(_.stmts)

    lir.Module(tpe, ports, instances, mems, hpStmts ++ components, inits, procedures)
  }

  def runInput(field: FieldContainer)(implicit stack: StackFrame, ctx: FirrtlContext, global: GlobalData): BuildResult[lir.Port] = {
    val stmts = field.code.flatMap(runStmt)

    val (portStmts, port) = field.ret.map(runExpr) match {
      case None => (Vector.empty, lir.Port(lir.Dir.Input, field.toFirrtlString, field.tpe))
      case Some(RunResult(stmts, inst)) =>
        val portName = NameTemplate.portPrefix + field.label.toString
        val portTpe = field.tpe.copy(flag = field.tpe.flag | BackendTypeFlag.DefaultInput)
        val port = lir.Port(lir.Dir.Input, portName, portTpe)
        val portActual = lir.Wire(field.label.toString, field.tpe)
        def portRef(name: String, tpe: BackendType): lir.SubField = lir.SubField(
          lir.Reference(portName, portTpe), name, tpe
        )

        val portActualRef = lir.Reference(portActual.name, portActual.tpe)
        val assignFromOuter = lir.Assign(portActualRef, portRef(NameTemplate.portBits, field.tpe))
        val assignFromDefault = lir.Assign(portActualRef, inst.asInstanceOf[DataInstance].refer)

        val condition = lir.When(
          portRef(NameTemplate.portActive, BackendType.boolTpe),
          Vector(assignFromOuter),
          Vector(assignFromDefault)
        )

        (stmts ++ Vector(portActual, condition), port)
    }

    BuildResult(stmts ++ portStmts, port)
  }

  def runOutput(field: FieldContainer)(implicit stack: StackFrame, ctx: FirrtlContext, global: GlobalData): BuildResult[lir.Port] = {
    val stmts = field.code.flatMap(runStmt)
    val fieldRef = lir.Reference(field.toFirrtlString, field.tpe)
    val retStmt = field.ret.map(runExpr) match {
      case None => Vector(lir.Invalid(fieldRef))
      case Some(RunResult(stmts, inst: DataInstance)) =>
        val connectOpt = lir.Assign(fieldRef, inst.refer)
        stmts :+ connectOpt
    }

    val port = lir.Port(lir.Dir.Output, field.toFirrtlString, field.tpe)

    BuildResult(stmts ++ retStmt, port)
  }

  def runInternal(field: FieldContainer)(implicit stack: StackFrame, ctx: FirrtlContext, global: GlobalData): BuildResult[lir.Wire] = {
    val stmts = field.code.flatMap(runStmt)
    val fieldRef = lir.Reference(field.toFirrtlString, field.tpe)
    val retStmt = field.ret.map(runExpr) match {
      case None => Vector(lir.Invalid(fieldRef))
      case Some(RunResult(stmts, inst: DataInstance)) =>
        stmts :+ lir.Assign(fieldRef, inst.refer)
    }

    val wire = lir.Wire(field.toFirrtlString, field.tpe)

    BuildResult(stmts ++ retStmt, wire)
  }

  def runRegister(field: FieldContainer)(implicit stack: StackFrame, ctx: FirrtlContext, global: GlobalData): BuildResult[lir.Reg] = {
    val stmts = field.code.flatMap(runStmt)
    val name = field.toFirrtlString

    val (defaultStmts, default) = field.ret.map(runExpr) match {
      case None => (Vector.empty, Option.empty)
      case Some(RunResult(eStmts, inst: DataInstance)) => (eStmts, inst.refer.some)
    }
    val reg = lir.Reg(name, default, field.tpe)

    BuildResult(stmts ++ defaultStmts, reg)
  }

  def runSubModule(field: FieldContainer)(implicit stack: StackFrame, ctx: FirrtlContext, global: GlobalData): BuildResult[(lir.SubModule, Vector[lir.When])] = {
    val stmts = field.code.flatMap(runStmt)
    val retStmts = field.ret
      .map(runExpr)
      .map { case RunResult(stmts, _) => stmts }
      .getOrElse(throw new ImplementationErrorException("sub module instance expression must be there"))

    val module = lir.SubModule(field.toFirrtlString, field.tpe)

    val subModuleStmts = stmts ++ retStmts
    val (whens, inits) = subModuleStmts.collectPartition { case when: lir.When => when }

    BuildResult(inits, (module, whens))
  }

  def runAlways(always: AlwaysContainer)(implicit stack: StackFrame, ctx: FirrtlContext, global: GlobalData): BuildResult[Unit] = {
    val stmts = always.code.flatMap(runStmt)
    BuildResult(stmts, ())
  }

  def runMemory(memory: FieldContainer)(implicit stack: StackFrame, ctx: FirrtlContext, global: GlobalData): BuildResult[lir.Memory] = {
    val dataType = memory.tpe.targs.head
    val HPElem.Num(depth) = memory.tpe.hargs(0)
    val HPElem.Num(readPort) = memory.tpe.hargs(2)
    val HPElem.Num(writePort) = memory.tpe.hargs(3)
    val HPElem.Num(readLatency) = memory.tpe.hargs(4)
    val HPElem.Num(writeLatency) = memory.tpe.hargs(5)

    val mem = lir.Memory(memory.label.toString, readPort, writePort, readLatency, writeLatency, depth, dataType, memory.tpe)
    BuildResult(Vector.empty, mem)
  }

  private def log2(x: Double): Double = math.log(x) / math.log(2)
  private def atLeastLength(x: Double): Int = math.ceil(log2(x + 1)).toInt

  def buildStageSignature(stage: StageContainer)(implicit stack: StackFrame, ctx: FirrtlContext, global: GlobalData): BuildResult[Vector[lir.Reg]] = {
    def buildParams(paramPairs: Vector[(String, BackendType)]): Vector[lir.Reg] = {
      paramPairs.foreach { case (name, _) => stack.lock(name) }

      val params = paramPairs
        .map { case (name, tpe) => stack.refer(name) -> tpe }
        .map { case (name, tpe) => name -> StructInstance(tpe, lir.Reference(name.name, tpe)) }

      params.foreach { case (name, instance) => stack.append(name, instance) }
      params.map{ case (name, inst) => lir.Reg(name.name, Option.empty, inst.tpe) }
    }

    val activeTpe = toBackendType(Type.bitTpe(1))
    val activeNode = lir.Node(stack.next("_GEN").name, lir.Literal(0, activeTpe), activeTpe)
    val activeRef = lir.Reference(activeNode.name, activeTpe)
    val active = lir.Reg(stage.activeName, Some(activeRef), activeTpe)

    val stageRegs = buildParams(stage.params.toVector)
    val stateRegs = buildParams(stage.states.flatMap(_.params))

    val stateLen = atLeastLength(stage.states.length)
    val stateTpe = toBackendType(Type.bitTpe(stateLen))
    val state =
      if (stage.states.isEmpty) None
      else Some(lir.Reg(
        stage.stateName,
        Option.empty,
        stateTpe
      ))

    val regs = active +: (stageRegs ++ stateRegs ++ state)

    BuildResult(Vector(activeNode), regs)
  }

  def runStage(stage: StageContainer)(implicit stack: StackFrame, ctx: FirrtlContext, global: GlobalData): BuildResult[lir.When] = {
    val stmts = stage.code.flatMap(runStmt)
    val statePairs = stage.states.zipWithIndex.map {
      case (state, idx) =>
        val stateLen = atLeastLength(stage.states.length).toInt
        val stateTpe = toBackendType(Type.bitTpe(stateLen))
        val stateStmts = state.code.flatMap(runStmt)
        val stateRef = lir.Reference(stage.stateName, stateTpe)

        val idxName = stack.next("_GEN")
        val idxLiteral = lir.Literal(idx, stateTpe)
        val idxNode = lir.Node(idxName.name, idxLiteral, stateTpe)
        val idxRef = lir.Reference(idxNode.name, stateTpe)

        val condNode = lir.Node(
          stack.next("_GEN").name,
          lir.Ops(PrimOps.Eq, Vector(stateRef, idxRef), Vector.empty, BackendType.boolTpe),
          BackendType.boolTpe
        )
        val condRef = lir.Reference(condNode.name, BackendType.boolTpe)
        val cond = lir.When (condRef, stateStmts, Vector.empty)

        (Vector(idxNode, condNode), cond)
    }
    val (stateNodess, states) = statePairs.unzip
    val stateNodes = stateNodess.flatten

    val cond = lir.When(
      lir.Reference(stage.activeName, BackendType.boolTpe),
      stmts ++ stateNodes ++ states,
      Vector.empty
    )

    BuildResult(Vector.empty, cond)
  }

  def buildProcSignature(proc: ProcContainer)(implicit stack: StackFrame, ctx: FirrtlContext, global: GlobalData): Vector[lir.Stmt] = {
    val paramss = proc.blks.map(_.params.toVector)
    val regs = paramss.flatMap(_.map{ case (name, tpe) => lir.Reg(name, Option.empty, tpe) })
    val idRegs = proc.blks
      .map{ blk =>
        val procPath = proc.label.symbol.path
        val blkName = blk.label.symbol.name
        val blkID = blk.label.idName

        lir.IDReg(procPath, blkName, blkID)
      }


    // add instances to stack
    regs.foreach{ r => stack.lock(r.name) }
    val instances = regs.map { reg => StructInstance(reg.tpe, lir.Reference(reg.name, reg.tpe)) }
    (regs zip instances).foreach{ case (reg, inst) => stack.append(Name(reg.name), inst) }

    val activeOff = lir.Literal(0, BackendType.boolTpe)
    val (activeOffNode, activeOffRef) = makeNode(activeOff)
    val blkActives = proc.blks
      .map(_.label.activeName)
      .map(name => lir.Reg(name, activeOffRef.some, BackendType.boolTpe))

    ((regs ++ idRegs) :+ activeOffNode) ++ blkActives
  }

  def runProc(proc: ProcContainer)(implicit stack: StackFrame, ctx: FirrtlContext, global: GlobalData): BuildResult[Vector[lir.When]] = {
    // for default expression
    val stmts = proc.default.flatMap(runStmt)
    val RunResult(exprStmts, defaultInst: DataInstance) = runExpr(proc.defaultRet)
    val defaultRet = lir.Return(proc.label.symbol.path, defaultInst.refer, Option.empty)
    val defaultStmts = stmts ++ exprStmts :+ defaultRet

    val blks = proc.blks.map { blk =>
      val stmts = blk.code.flatMap(runStmt)
      val activeRef = lir.Reference(blk.label.activeName, BackendType.boolTpe)
      lir.When(activeRef, stmts, Vector.empty)
    }

    BuildResult(defaultStmts, blks)
  }

  private def buildInputInterfaceSignature(interface: MethodContainer)(implicit stack: StackFrame, global: GlobalData): BuildResult[Vector[lir.Port]] = {
    interface.params.foreach { case (name, _) => stack.lock(name) }
    val params = interface.params
      .map { case (name, tpe) => stack.refer(name) -> tpe }
      .map { case (name, tpe) => name -> DataInstance(tpe, lir.Reference(name.name, tpe)) }
      .toVector
    params.foreach { case (name, instance) => stack.append(name, instance) }

    val retTpe = interface.label.symbol.tpe.asMethodType.returnType
    val isUnitRet = retTpe.origin == Symbol.unit

    val active = lir.Port(lir.Dir.Input, interface.activeName, BackendType.boolTpe)
    val paramPorts = params.map { case (name, inst) => lir.Port(lir.Dir.Input, name.name, inst.tpe) }
    val retName =
      if(isUnitRet) None
      else Some(interface.retName)

    val output = retName.map(name => lir.Port(lir.Dir.Output, name, interface.retTpe))
    val retInvalid = retName
      .map(name => lir.Reference(name, interface.retTpe))
      .map(ref => lir.Invalid(ref))

    val ports = active +: (paramPorts ++ output)

    BuildResult(retInvalid.toVector, ports)
  }

  private def buildInternalInterfaceSignature(interface: MethodContainer)(implicit stack: StackFrame, global: GlobalData): BuildResult[Vector[lir.Stmt]] = {
    interface.params.foreach { case (name, _) => stack.lock(name) }
    val retTpe = interface.label.symbol.tpe.asMethodType.returnType
    val isUnitRet = retTpe.origin == Symbol.unit

    val params = interface.params
      .map { case (name, tpe) => stack.refer(name) -> tpe }
      .map { case (name, tpe) => name -> DataInstance(tpe, lir.Reference(name.name, tpe)) }
      .toVector
    params.foreach { case (name, instance) => stack.append(name, instance) }

    val active = lir.Wire(interface.activeName, BackendType.boolTpe)
    val (activeOffNode, activeOffRef) = makeNode(lir.Literal(0, BackendType.boolTpe))
    val activeOff = lir.Assign(lir.Reference(interface.activeName, BackendType.boolTpe), activeOffRef)

    val paramWires = params.map{ case (name, ref) => lir.Wire(name.name, ref.tpe)}
    val retWireOpt =
      if(isUnitRet) Option.empty
      else Some(lir.Wire(interface.retName, interface.retTpe))
    val sigWires = paramWires ++ retWireOpt
    val wireRefs = sigWires.map(w => lir.Reference(w.name, w.tpe))
    val invalids = wireRefs.map(ref => lir.Invalid(ref))

    val wires = active +: sigWires
    val inits = Vector(activeOffNode, activeOff) ++ invalids

    BuildResult(inits, wires)
  }

  def runInterface(interface: MethodContainer)(implicit stack: StackFrame, ctx: FirrtlContext, global: GlobalData): BuildResult[lir.When] = {
    val stmts = removeUnitNode(interface.code.flatMap(runStmt(_)))
    val RunResult(retStmtTmps, instance: DataInstance) = runExpr(interface.ret)
    val retStmts = removeUnitNode(retStmtTmps)
    val methodRetTpe = interface.label.symbol.tpe.asMethodType.returnType
    val retConnect =
      if (methodRetTpe == Type.unitTpe) Option.empty
      else lir.Assign(lir.Reference(interface.retName, interface.retTpe), instance.refer).some

    val cond = lir.When(lir.Reference(interface.activeName, BackendType.boolTpe), stmts ++ retStmts ++ retConnect, Vector.empty)

    BuildResult(Vector.empty, cond)
  }

  def buildUpperModule(moduleName: String, tpe: BackendType)(implicit stack: StackFrame, ctx: FirrtlContext, global: GlobalData): (Vector[lir.Port], Vector[lir.Stmt]) = {
    val allInterfaces = ctx.interfaces.getOrElse(tpe, Vector.empty)

    val interfaces = allInterfaces.filter {
      interface =>
        val isSibling = interface.label.symbol.hasFlag(Modifier.Sibling)
        val isParent = interface.label.symbol.hasFlag(Modifier.Parent)

        isSibling || isParent
    }

    val pairs = interfaces.map {
      interface =>
        def buildName(name: String): String = moduleName + "_" + name

        val activeName = buildName(interface.activeName)
        val retName = buildName(interface.retName)

        val active = lir.Port(lir.Dir.Output, activeName, BackendType.boolTpe)
        val retOpt =
          if (interface.ret.tpe == toBackendType(Type.unitTpe)) Option.empty
          else lir.Port(lir.Dir.Input, retName, interface.ret.tpe).some
        val params = interface.params.map { case (name, tpe) => lir.Port(lir.Dir.Output, buildName(name), tpe) }.toVector

        val (litNode, litRef) = makeNode(lir.Literal(0, BackendType.boolTpe))
        val activeRef = lir.Reference(activeName, BackendType.boolTpe)
        val activeInit = lir.Assign(activeRef, litRef)
        val paramInits = params
          .map(param => lir.Reference(param.name, param.tpe))
          .map(ref => lir.Invalid(ref))

        (active +: (params ++ retOpt), Vector(litNode, activeInit) ++ paramInits)
    }

    val (ports, inits) = pairs.unzip

    (ports.flatten, inits.flatten)
  }

  def runStmt(stmt: backend.Stmt)(implicit stack: StackFrame, ctx: FirrtlContext, global: GlobalData): Vector[lir.Stmt] = {
    def buildConnect(loc: lir.Ref, expr: backend.Expr): (Instance, Vector[lir.Stmt]) = {
      val RunResult(stmts, instance) = runExpr(expr)

      val (retInst, connectOpt) = instance match {
        case _: ModuleInstance => (instance, Option.empty)
        case inst @ DataInstance(tpe, _) =>
          val assign = lir.Assign(loc, inst.refer)
          val instance = DataInstance(tpe, loc)

          (instance, assign.some)
      }

      (retInst, stmts ++ connectOpt)
    }

    stmt match {
      case backend.Variable(name, tpe, expr) =>
        val varName = stack.next(name)
        val wire = lir.Wire(varName.name, tpe)
        val varRef = lir.Reference(varName.name, tpe)

        val (inst, stmts) = buildConnect(varRef, expr)

        stack.append(varName, inst)
        wire +: stmts
      case backend.Temp(id, expr) =>
        val tempName = stack.next(id)
        val RunResult(exprStmts, instance) = runExpr(expr)

        val (nodeInst, nodeOpt) = instance match {
          case inst: ModuleInstance => (inst,Option.empty)
          case inst @ DataInstance(tpe, _) =>
            val node = lir.Node(tempName.name, inst.refer, tpe)
            val retInst = DataInstance(tpe, lir.Reference(tempName.name, tpe))

            (retInst, node.some)
        }

        stack.append(tempName, nodeInst)
        exprStmts ++ nodeOpt
      case backend.Assign(target, expr) if target.head._2.symbol.isModuleTypeSymbol =>
        val (moduleName, moduleTpe) = target.head
        val (portName, rawTpe) = target.tail.head
        val input = ctx.inputs.get(moduleTpe).flatMap(_.find(_.label.toString == portName)).get
        def portRef(name: String, tpe: BackendType): lir.SubField = lir.SubField(lir.Reference(moduleName, moduleTpe), name, tpe)

        input.ret match {
          case None    => buildConnect(portRef(portName, rawTpe), expr)._2
          case Some(_) =>
            val portTpe = rawTpe.copy(flag = rawTpe.flag | BackendTypeFlag.DefaultInput)
            val port = portRef(NameTemplate.portPrefix ++ portName, portTpe)
            val (_, stmts)  = buildConnect(lir.SubField(port, NameTemplate.portBits, portTpe), expr)
            val (trueNode, trueRef) = makeNode(lir.Literal(1, BackendType.boolTpe))
            val assignValid =  lir.Assign(lir.SubField(port, NameTemplate.portActive, BackendType.boolTpe), trueRef)

            stmts ++ Vector(trueNode, assignValid)
        }

      case backend.Assign(target, expr) =>
        val (headName, headTpe) = target.head
        val loc = target.tail.foldLeft[lir.Ref](lir.Reference(headName, headTpe)) {
          case (ref, (name, tpe)) => lir.SubField(ref, name, tpe)
        }

        val (_, stmts) = buildConnect(loc, expr)
        stmts
      case backend.Abandon(expr) => runExpr(expr).stmts
    }
  }


  def runExpr(expr: backend.Expr)(implicit stack: StackFrame, ctx: FirrtlContext, global: GlobalData): RunResult =
    expr match {
      case ident: backend.Ident => runIdent(ident)
      case refer: backend.ReferField => runReferField(refer)
      case _: backend.This => runThis()
      case construct: backend.ConstructStruct => runConstructStruct(construct)
      case construct: backend.ConstructModule => runConstructModule(construct)
      case construct: backend.ConstructMemory => runConstructMemory(construct)
      case construct: backend.ConstructEnum => runConstructEnum(construct)
      case call: backend.CallMethod => runCallMethod(call)
      case call: backend.CallInterface => runCallInterface(call)
      case call: backend.CallBuiltIn => runCallBuiltIn(call)
      case read: backend.ReadMemory => runReadMemory(read)
      case write: backend.WriteMemory => runWriteMemory(write)
      case ifExpr: backend.IfExpr => runIfExpr(ifExpr)
      case matchExpr: backend.Match => runMatch(matchExpr)
      case finish: backend.Finish => runFinish(finish)
      case goto: backend.Goto => runGoto(goto)
      case generate: backend.Generate => runGenerate(generate)
      case ret: backend.Return => runReturn(ret)
      case commence: backend.Commence => runCommence(commence)
      case relay: backend.RelayBlock => runRelayBlock(relay)
      case deref: backend.Deref => runDeref(deref)
      case backend.IntLiteral(value) => DataInstance.int(value)
      case backend.BoolLiteral(value) => DataInstance.bool(value)
      case backend.UnitLiteral() => DataInstance.unit()
      case bit @ backend.BitLiteral(value, HPElem.Num(width)) =>
        val (bitNode, bitRef) = makeNode(lir.Literal(value, BackendType.bitTpe(width)))
        val instance = StructInstance(bit.tpe, bitRef)
        RunResult(Vector(bitNode), instance)
    }

  def runIdent(ident: backend.Ident)(implicit stack: StackFrame, ctx: FirrtlContext, global: GlobalData): RunResult = {
    val name = stack.refer(ident.id.name)
    RunResult(Vector.empty, stack.lookup(name))
  }

  def runReferField(referField: backend.ReferField)(implicit stack: StackFrame, ctx: FirrtlContext, global: GlobalData): RunResult = {
    val accessor = referField.accessor match {
      case backend.Term.Temp(id, _) => stack.lookup(stack.refer(id))
      case backend.Term.Variable(name, _) => stack.lookup(stack.refer(name))
    }

    val instance = accessor match {
      case DataInstance(_, refer) =>
        val subField = lir.SubField(refer, referField.field.toString, referField.tpe)
        StructInstance(referField.tpe, subField)
      case ModuleInstance(_, ModuleLocation.Sub(refer)) =>
        val subField = lir.SubField(refer, referField.field.toString, referField.tpe)
        val tpe = referField.tpe

        referField.field.symbol.tpe.asRefType.origin match {
          case _: Symbol.ModuleSymbol => throw new ImplementationErrorException("module instance must be referred directly")
          case _ => StructInstance(tpe, subField)
        }
      case ModuleInstance(_, ModuleLocation.This) =>
        val tpe = referField.tpe
        val fieldSymbol = referField.field.symbol
        fieldSymbol.tpe.asRefType.origin match {
          case _: Symbol.ModuleSymbol if fieldSymbol.hasFlag(Modifier.Parent) =>
            ModuleInstance(tpe, ModuleLocation.Upper(referField.field.toString))
          case _: Symbol.ModuleSymbol if fieldSymbol.hasFlag(Modifier.Sibling) =>
            ModuleInstance(tpe, ModuleLocation.Upper(referField.field.toString))
          case _: Symbol.ModuleSymbol =>
            val reference = lir.Reference(referField.field.toString, referField.tpe)
            ModuleInstance(tpe, ModuleLocation.Sub(reference))
          case _ =>
            val reference = lir.Reference(referField.field.toString, referField.tpe)
            StructInstance(tpe, reference)
        }
      case ModuleInstance(_, ModuleLocation.Upper(_)) =>
        throw new ImplementationErrorException("compiler does not support to refer upper module's field")
    }

    RunResult(Vector.empty, instance)
  }

  def runCallMethod(call: backend.CallMethod)(implicit stack: StackFrame, ctx: FirrtlContext, global: GlobalData): RunResult = {
    def getInstance(term: backend.Term): Instance = {
      val name = term match {
        case backend.Term.Temp(id, _) => stack.refer(id)
        case backend.Term.Variable(name, _) => stack.refer(name)
      }

      stack.lookup(name)
    }

    val method = call.label.accessor match {
      case Some(tpe) =>
        ctx.methods(tpe).find(_.label == call.label).get
      case None => ctx.functions.find(_.label == call.label).get
    }

    val accessor = call.accessor.map(getInstance)
    val args = call.args.map(getInstance)
    val hargResults = call.hargs.map {
      case HPElem.Num(value) => DataInstance.int(value)
      case HPElem.Str(value) => RunResult(Vector.empty, StringInstance(value))
    }
    val hargs = hargResults.map(_.instance)
    val hargStmts = hargResults.flatMap(_.stmts)

    val newStack = StackFrame(stack, accessor, isBlockStack = false)

    val hargNames = method.hparams.keys.map(newStack.next)
    val argNames = method.params.keys.map(newStack.next)

    (hargNames zip hargs).foreach { case (name, harg) => newStack.append(name, harg) }
    (argNames zip args).foreach { case (name, arg) => newStack.append(name, arg) }

    val stmts = method.code.flatMap(stmt => runStmt(stmt)(newStack, ctx, global))
    val RunResult(retStmts, instance) = runExpr(method.ret)(newStack, ctx, global)

    RunResult(hargStmts ++ stmts ++ retStmts, instance)
  }

  def runCallInterface(call: backend.CallInterface)(implicit stack: StackFrame, ctx: FirrtlContext, global: GlobalData): RunResult = {
    def calling(tpe: BackendType)(refer: (String, BackendType) => lir.Ref): RunResult = {
      val candidates = ctx.interfaces(tpe)
      val interface = candidates.find(_.label == call.label).get

      val params = interface.params.toVector.map{ case (name, tpe) => refer(name, tpe) }
      val argNames = call.args.map {
        case backend.Term.Temp(id, _) => stack.refer(id)
        case backend.Term.Variable(name, _) => stack.refer(name)
      }
      val args = argNames.map(stack.lookup).map(_.asInstanceOf[DataInstance])
      val (litNode, litRef) = makeNode(lir.Literal(1, BackendType.boolTpe))
      val activate = lir.Assign(
        refer(interface.activeName, BackendType.boolTpe),
        litRef
      )

      val connects = (params zip args).map{ case (p, a) => lir.Assign(p, a.refer) }
      val result = interface.ret match {
        case backend.UnitLiteral() => DataInstance.unit()
        case _ =>
          val tpe = interface.retTpe
          RunResult(Vector.empty, DataInstance(tpe, refer(interface.retName, tpe)))
      }

      RunResult(Vector(litNode, activate) ++ connects ++ result.stmts, result.instance)
    }

    val referName = call.accessor match {
      case backend.Term.Temp(id, _) => stack.refer(id)
      case backend.Term.Variable(name, _) => stack.refer(name)
    }

    stack.lookup(referName) match {
      case ModuleInstance(tpe, ModuleLocation.This) => calling(tpe){ case (name, tpe) => lir.Reference(name, tpe) }
      case ModuleInstance(tpe, ModuleLocation.Sub(refer)) => calling(tpe){ case (name, tpe) => lir.SubField(refer, name, tpe) }
      case ModuleInstance(tpe, ModuleLocation.Upper(refer)) => calling(tpe){ case (name, tpe) => lir.Reference(refer + "_" + name, tpe) }
    }
  }

  def runCallBuiltIn(call: backend.CallBuiltIn)(implicit stack: StackFrame, ctx: FirrtlContext, global: GlobalData): RunResult = {
    def getInstance(term: backend.Term): Instance =
      term match {
        case backend.Term.Temp(id, _) => stack.lookup(stack.refer(id))
        case backend.Term.Variable(name, _) => stack.lookup(stack.refer(name))
      }

    val insts = call.args.map(getInstance)

    call.label match {
      case "addInt" => builtin.intAdd(insts(0), insts(1), stack)
      case "subInt" => builtin.intSub(insts(0), insts(1), stack)
      case "mulInt" => builtin.intMul(insts(0), insts(1), stack)
      case "divInt" => builtin.intDiv(insts(0), insts(1), stack)
      case "orInt"  => builtin.intOr(insts(0), insts(1), stack)
      case "andInt" => builtin.intAnd(insts(0), insts(1), stack)
      case "xorInt" => builtin.intXor(insts(0), insts(1), stack)
      case "shlInt" => builtin.intShl(insts(0), insts(1))
      case "shrInt" => builtin.intShr(insts(0), insts(1))
      case "dynShlInt" => builtin.intDynShl(insts(0), insts(1))
      case "dynShrInt" => builtin.intDynShr(insts(0), insts(1))
      case "eqInt" => builtin.intEq(insts(0), insts(1), stack, global)
      case "neInt" => builtin.intNe(insts(0), insts(1), stack, global)
      case "gtInt" => builtin.intGt(insts(0), insts(1), stack, global)
      case "geInt" => builtin.intGe(insts(0), insts(1), stack, global)
      case "ltInt" => builtin.intLt(insts(0), insts(1), stack, global)
      case "leInt" => builtin.intLe(insts(0), insts(1), stack, global)
      case "negInt" => builtin.intNeg(insts(0), stack, global)
      case "notInt" => builtin.intNot(insts(0), stack, global)
      case "orBool"  => builtin.bitOr(insts(0), insts(1))
      case "andBool" => builtin.bitAnd(insts(0), insts(1))
      case "xorBool" => builtin.bitXor(insts(0), insts(1))
      case "eqBool" => builtin.bitEq(insts(0), insts(1), stack, global)
      case "neBool" => builtin.bitNe(insts(0), insts(1), stack, global)
      case "notBool" => builtin.bitNot(insts(0))
      case "addBit" => builtin.bitAdd(insts(0), insts(1))
      case "subBit" => builtin.bitSub(insts(0), insts(1))
      case "mulBit" => builtin.bitMul(insts(0), insts(1))
      case "divBit" => builtin.bitDiv(insts(0), insts(1))
      case "orBit"  => builtin.bitOr(insts(0), insts(1))
      case "andBit" => builtin.bitAnd(insts(0), insts(1))
      case "xorBit" => builtin.bitXor(insts(0), insts(1))
      case "shlBit" => builtin.bitShl(insts(0), insts(1))
      case "shrBit" => builtin.bitShr(insts(0), insts(1))
      case "dynShlBit" => builtin.bitDynShl(insts(0), insts(1))
      case "dynShrBit" => builtin.bitDynShr(insts(0), insts(1))
      case "eqBit" => builtin.bitEq(insts(0), insts(1), stack, global)
      case "neBit" => builtin.bitNe(insts(0), insts(1), stack, global)
      case "gtBit" => builtin.bitGt(insts(0), insts(1), stack, global)
      case "geBit" => builtin.bitGe(insts(0), insts(1), stack, global)
      case "ltBit" => builtin.bitLt(insts(0), insts(1), stack, global)
      case "leBit" => builtin.bitLe(insts(0), insts(1), stack, global)
      case "negBit" => builtin.bitNeg(insts(0))
      case "notBit" => builtin.bitNot(insts(0))
      case "signExtBit" => builtin.bitSignExt(call.accessorTpe.get, insts(0), stack, global)
      case "truncateBit" => builtin.bitTruncate(insts(0), call.hargs(0), call.hargs(1), stack, global)
      case "bitBit" => builtin.bitBit(insts(0), call.hargs(0), stack, global)
      case "concatBit" => builtin.bitConcat(insts(0), insts(1), stack, global)
      case "idxVec" => builtin.vecIdx(insts(0), call.hargs(0), global)
      case "idxDynVec" => builtin.vecIdxDyn(insts(0), insts(1), global)
      case "updatedVec" => builtin.vecUpdated(insts(0), insts(1), call.hargs(0))
      case "updatedDynVec" => builtin.vecUpdatedDyn(insts(0), insts(1), insts(2))
      case "truncateVec" => builtin.vecTruncate(insts(0), call.hargs(0), call.hargs(1))
      case "appendVec" => builtin.vecAppend(insts(0), insts(1))
      case "emptyVec" => builtin.vecEmpty(call.accessorTpe.get)
      case "fromIntBit" => builtin.bitFromInt(call.accessorTpe.get, insts(0))
      case "fromBoolBit" => builtin.bitFromBool(call.accessorTpe.get, insts(0))
      case "fromBitBit" => builtin.bitFromBit(call.accessorTpe.get, insts(0))
    }
  }

  def  runReadMemory(read: backend.ReadMemory)(implicit stack: StackFrame, ctx: FirrtlContext, global: GlobalData): RunResult = {
    def getName(term: backend.Term): Name = term match {
      case backend.Term.Variable(name, _) => stack.refer(name)
      case backend.Term.Temp(id, _) => stack.refer(id)
    }

    val ModuleInstance(_, location) = stack.lookup(getName(read.accessor))
    val ModuleLocation.Sub(lir.Reference(memName, _)) = location
    val DataInstance(_, addrRef) = stack.lookup(getName(read.addr))

    val readTpe = read.tpe.copy(flag = read.tpe.flag | BackendTypeFlag.Pointer)
    val readStmt = lir.MemRead(memName, read.port, addrRef, readTpe)
    val readDataID = lir.MemPortID(memName, read.port, readTpe)
    val pointerNode = lir.Node(stack.next(NameTemplate.temp).name, readDataID, readTpe)
    val nodeRef = lir.Reference(pointerNode.name, pointerNode.tpe)

    val instance = DataInstance(readTpe, nodeRef)

    RunResult(Vector(readStmt, pointerNode), instance)
  }

  def runWriteMemory(write: backend.WriteMemory)(implicit stack: StackFrame, ctx: FirrtlContext, global: GlobalData): RunResult = {
    def getName(term: backend.Term): Name = term match {
      case backend.Term.Variable(name, _) => stack.refer(name)
      case backend.Term.Temp(id, _) => stack.refer(id)
    }

    val ModuleInstance(_, location) = stack.lookup(getName(write.accessor))
    val ModuleLocation.Sub(memory) = location
    val DataInstance(_, addrRef) = stack.lookup(getName(write.addr))
    val DataInstance(_, dataRef) = stack.lookup(getName(write.data))

    val writeMem = lir.MemWrite(memory.name, write.port, addrRef, dataRef)
    val result = DataInstance.unit()

    RunResult(writeMem +: result.stmts, result.instance)
  }

  def runThis()(implicit stack: StackFrame, ctx: FirrtlContext, global: GlobalData): RunResult =
    RunResult(Vector.empty, stack.lookupThis.get)

  def runIfExpr(ifExpr: backend.IfExpr)(implicit stack: StackFrame, ctx: FirrtlContext, global: GlobalData): RunResult = {
    def runInner(stmts: Vector[backend.Stmt], last: backend.Expr): RunResult = {
      val innerStmts = stmts.flatMap(runStmt)
      val RunResult(lastStmts, instance) = runExpr(last)

      val allStmts = innerStmts ++ lastStmts
      RunResult(allStmts, instance)
    }

    val condName = stack.refer(ifExpr.cond.id)
    val DataInstance(_, condRef) = stack.lookup(condName)

    lazy val retName = stack.next("_IFRET")

    val wireOpt =
      if(ifExpr.tpe == BackendType.unitTpe) None
      else lir.Wire(retName.name, ifExpr.tpe).some
    val retRefOpt = wireOpt.map(w => lir.Reference(w.name, w.tpe))

    val RunResult(conseqStmts, conseqInst: DataInstance) = runInner(ifExpr.conseq, ifExpr.conseqLast)
    val RunResult(altStmts, altInst: DataInstance) = runInner(ifExpr.alt, ifExpr.altLast)

    val conseqAssign = retRefOpt.map(ref => lir.Assign(ref, conseqInst.refer))
    val altAssign = retRefOpt.map(ref => lir.Assign(ref, altInst.refer))
    val whenStmt = lir.When(
      condRef,
      conseqStmts ++ conseqAssign,
      altStmts ++ altAssign
    )

    val retResult = retRefOpt
      .map(ret => RunResult(Vector.empty, DataInstance(ifExpr.tpe, ret)))
      .getOrElse(DataInstance.unit())
    val stmts = wireOpt.toVector :+ whenStmt

    RunResult(stmts ++ retResult.stmts, retResult.instance)
  }

  def runMatch(matchExpr: backend.Match)(implicit stack: StackFrame, ctx: FirrtlContext, global: GlobalData): RunResult = {
    def extractFieldData(baseRef: lir.SubField, source: lir.Ref, srcTpe: BackendType, history: Vector[BackendType], localStack: StackFrame): (Vector[lir.Stmt], Name, Vector[BackendType]) = {
      def convertHWType(tpe: BackendType): BackendType = tpe.symbol match {
        case sym if sym == Symbol.int => BackendType.intTpe
        case sym if sym == Symbol.unit => BackendType.unitTpe
        case _ => tpe
      }

      def extractMono(tpe: BackendType): (Vector[lir.Node], Name, Vector[BackendType]) = {
        val name = localStack.next("_EXTRACT")
        val addedHistory = tpe +: history
        val expr = lir.Extract(baseRef, addedHistory, tpe)
        val node = lir.Node(name.name, expr, tpe)

        (Vector(node), name, addedHistory)
      }

      val tpe = convertHWType(srcTpe)

      tpe.symbol match {
        case _ if tpe.flag.hasFlag(BackendTypeFlag.Pointer) => extractMono(tpe)
        case sym if sym == Symbol.int => extractMono(BackendType.intTpe)
        case sym if sym == Symbol.bool => extractMono(BackendType.boolTpe)
        case sym if sym == Symbol.unit => extractMono(BackendType.unitTpe)
        case sym if sym == Symbol.bit =>
          val HPElem.Num(width) = tpe.hargs(0)
          extractMono(BackendType.bitTpe(width))
        case sym if sym == Symbol.vec =>
          val vecName = localStack.next("_EXTRACT")
          val wire = lir.Wire(vecName.name, tpe)
          val wireRef = lir.Reference(wire.name, wire.tpe)
          val HPElem.Num(length) = tpe.hargs(0)
          val elemTpe = tpe.targs(0)

          val (stmts, addedHistory) = (0 until length).foldLeft(Vector.empty[lir.Stmt], history){
            case ((stmts, history), idx) =>
              val subFieldRef = lir.SubIndex(source, idx, elemTpe)
              val (leafStmts, name, addedHistory) = extractFieldData(baseRef, subFieldRef, elemTpe, history, localStack)
              val assign = lir.Assign(
                lir.SubIndex(wireRef, idx, elemTpe),
                lir.Reference(name.name, elemTpe)
              )

              (stmts ++ leafStmts :+ assign, addedHistory)
          }

          (wire +: stmts, vecName, addedHistory)
        case sym if sym.isEnumSymbol =>
          val enumName = localStack.next("_EXTRACT")
          val wire = lir.Wire(enumName.name, tpe)
          val wireRef = lir.Reference(wire.name, tpe)

          val memberTpe = tpe.copy(flag = tpe.flag | BackendTypeFlag.EnumFlag)
          val dataTpe = tpe.copy(flag = tpe.flag | BackendTypeFlag.EnumData)

          val member = lir.Extract(source, memberTpe +: history, memberTpe)
          val data = lir.Extract(source, Vector(dataTpe, memberTpe) ++ history, dataTpe)
          val memberRef = lir.SubField(wireRef, NameTemplate.enumFlag, memberTpe)
          val dataRef = lir.SubField(wireRef, NameTemplate.enumData, dataTpe)
          val (memberNode, memberNodeRef) = makeNode(member)(localStack)
          val (dataNode, dataNodeRef) = makeNode(data)(localStack)
          val assignData = lir.Assign(dataRef, dataNodeRef)
          val assignMember = lir.Assign(memberRef, memberNodeRef)

          val stmts = Vector(wire, memberNode, dataNode, assignMember, assignData)
          val addedHistory = Vector(dataTpe, memberTpe) ++ history

          (stmts, enumName, addedHistory)
        case _ =>
          val bundleName = localStack.next("_EXTRACT")
          val wire = lir.Wire(bundleName.name, tpe)
          val fields = tpe.fields.toVector.sortWith{ case ((left, _), (right, _)) => left < right }

          val (stmts, nextIdx) = fields.foldLeft((Vector.empty[lir.Stmt], history)) {
            case ((stmts, history), (name, fieldTpe)) =>
              val subField = lir.SubField(source, name, fieldTpe)
              val (leafStmts, extractName, addedHistory) = extractFieldData(baseRef, subField, fieldTpe, history, localStack)
              val dstField = lir.SubField(lir.Reference(bundleName.name, tpe), name, fieldTpe)
              val extractField = lir.Reference(extractName.name, fieldTpe)
              val assign = lir.Assign(dstField, extractField)

              (stmts ++ leafStmts :+ assign, addedHistory)
          }

          (wire +: stmts, bundleName, nextIdx)
      }
    }

    def runPattern(instance: DataInstance, pattern: backend.MatchPattern, caseStack: StackFrame): RunResult = {
      def toLIRForm(lit: backend.Literal): lir.Literal = {
        def toLit(value: Int, tpe: BackendType): lir.Literal = lir.Literal(value, tpe)

        lit match {
          case backend.IntLiteral(value) => toLit(value, BackendType.intTpe)
          case backend.BitLiteral(value, HPElem.Num(width)) => toLit(value.toInt, BackendType.bitTpe(width))
          case backend.BoolLiteral(value) => toLit(if(value) 1 else 0, BackendType.boolTpe)
          case backend.UnitLiteral() => toLit(0, BackendType.unitTpe)
        }
      }

      def literalPattern(lit: backend.Literal): RunResult = {
        val locName = caseStack.next("_GEN")
        val loc = lir.Reference(locName.name, lit.tpe)
        val literal = toLIRForm(lit)
        val (literalNode, literalRef) = makeNode(literal)(caseStack)
        val cmp = lir.Ops(PrimOps.Eq, Vector(instance.refer, literalRef), Vector.empty, BackendType.boolTpe)
        val node = lir.Node(locName.name, cmp, BackendType.boolTpe)
        val inst = DataInstance(BackendType.boolTpe, lir.Reference(node.name, node.tpe))

        RunResult(Vector(literalNode, node), inst)
      }

      def identPattern(variable: backend.Term.Variable): RunResult = {
        val locName = caseStack.next(variable.name)
        val loc = lir.Reference(locName.name, variable.tpe)
        val node = lir.Node(locName.name, instance.refer, variable.tpe)
        val locInstance = DataInstance(instance.tpe, loc)
        caseStack.append(locName, locInstance)
        val RunResult(stmts, inst: DataInstance) = DataInstance.bool(bool = true)(caseStack, global)

        RunResult(node +: stmts, inst)
      }

      pattern match {
        case backend.WildCardPattern(_) => DataInstance.bool(bool = true)(caseStack, global)
        case backend.LiteralPattern(lit) => literalPattern(lit)
        case backend.IdentPattern(name) => identPattern(name)
        case backend.EnumPattern(variant, patterns, tpe) =>
          val memberTpe = tpe.copy(flag = tpe.flag | BackendTypeFlag.EnumFlag)
          val memberRef = lir.SubField(instance.refer, "_member", memberTpe)

          val dataTpe = tpe.copy(flag = tpe.flag | BackendTypeFlag.EnumData)
          val dataRef = lir.SubField(instance.refer, "_data", dataTpe)

          val (litNode, litRef) = makeNode(lir.Literal(variant, memberTpe))(caseStack)
          val variantEq = lir.Ops(
            PrimOps.Eq,
            Vector(memberRef, litRef),
            Vector.empty,
            BackendType.boolTpe
          )

          val stmtBuilder = Vector.newBuilder[lir.Stmt]
          val refBuilder = Vector.newBuilder[lir.Reference]
          patterns.map(_.tpe).scanLeft(Vector.empty[BackendType]) {
            case (history, tpe) =>
              val (stmts, name, addedHistory) = extractFieldData(dataRef, dataRef, tpe, history, caseStack)
              stmtBuilder ++= stmts
              refBuilder += lir.Reference(name.name, tpe)

              addedHistory
          }

          val stmts = stmtBuilder.result()
          val refs = refBuilder.result()

          val trueRef = lir.Literal(1, BackendType.boolTpe)
          val results = (patterns zip refs)
            .map{ case (pattern, ref) => pattern -> DataInstance(pattern.tpe, ref) }
            .map{ case (pattern, inst) => runPattern(inst, pattern, caseStack) }

          val conds = results.map(_.instance.asInstanceOf[DataInstance])
          val patternStmts = results.flatMap(_.stmts)

          val leftNodes = Vector.newBuilder[lir.Node]
          val condition = conds.foldLeft[lir.Expr](variantEq) {
            case (left, right) =>
              val (leftNode, leftRef) = makeNode(left)(caseStack)
              leftNodes += leftNode

              lir.Ops(
                PrimOps.And,
                Vector(leftRef, right.refer),
                Vector.empty,
                left.tpe
            )
          }

          val condName = caseStack.next("_GEN")
          val condRef = lir.Reference(condName.name, condition.tpe)
          val connect = lir.Node(condName.name, condition, condition.tpe)
          val returnStmts = litNode +: ((stmts ++ patternStmts) ++ (leftNodes.result() :+ connect))
          val returnInst = DataInstance(BackendType.boolTpe, condRef)

          RunResult(returnStmts, returnInst)
      }
    }

    def runCase(instance: DataInstance, caseExpr: backend.Case, retLoc: Option[lir.Reference]): (Vector[lir.Stmt], lir.When) = {
      val newStack = StackFrame(stack, stack.lookupThis, isBlockStack = true)
      val RunResult(patternStmts, condInstance: DataInstance) = runPattern(instance, caseExpr.pattern, newStack)
      val bodyStmts = caseExpr.stmts.flatMap(runStmt(_)(newStack, ctx, global))
      val RunResult(exprStmts, retInstance: DataInstance) = runExpr(caseExpr.ret)(newStack, ctx, global)

      val retConnect = retLoc.map(loc => lir.Assign(loc, retInstance.refer))
      val conseqStmts = bodyStmts ++ exprStmts ++ retConnect
      val when = lir.When(condInstance.refer, conseqStmts, Vector.empty)

      (patternStmts, when)
    }

    val backend.Match(matched, cases, tpe, _) = matchExpr
    val instance = stack.lookup(stack.refer(matched.id))

    val retWireOpt =
      if(tpe.symbol == Symbol.unit) None
      else {
        val retName = stack.next("_GEN")
        lir.Wire(retName.name, tpe).some
      }

    val retRefOpt = retWireOpt.map(wire => lir.Reference(wire.name, wire.tpe))
    val RunResult(resStmts, retInstance) = retRefOpt.map(ref => RunResult(Vector.empty, DataInstance(tpe, ref))).getOrElse(DataInstance.unit())
    val retInvalid = retRefOpt.map(ref => lir.Invalid(ref))
    val retStmts = Vector(retWireOpt, retInvalid).flatten

    retRefOpt.foreach(ref => stack.append(Name(ref.name), retInstance))

    val (patternStmtss, conds) = cases.map(runCase(instance.asInstanceOf[DataInstance], _, retRefOpt)).unzip

    val patternStmts = patternStmtss.flatten
    val errorMsg = s"Pattern matching is failed at [${matchExpr.pos}]\n"
    val caseConds = conds.foldRight[lir.Stmt](lir.Stop(errorMsg)) {
      case (cond, elsePart) =>  cond.copy(alt = Vector(elsePart))
    }

    val stmts = resStmts ++ retStmts ++ patternStmts :+ caseConds

    RunResult(stmts, retInstance)
  }

  def runConstructStruct(construct: backend.ConstructStruct)(implicit stack: StackFrame, ctx: FirrtlContext, global: GlobalData): RunResult = {
    val results = construct.pairs.map { case (key, value) => key -> runExpr(value) }
    val stmts = results.values.foldLeft(Vector.empty[lir.Stmt]) {
      case (stmts, result) => stmts ++ result.stmts
    }

    val bundleName = stack.next("_BUNDLE")
    val bundleWire = lir.Wire(bundleName.name, construct.tpe)
    val bundleRef = lir.Reference(bundleName.name, construct.tpe)
    val instance = DataInstance(construct.tpe, bundleRef)
    stack.append(bundleName, instance)

    val assigns = results.toVector.map {
      case (name, RunResult(_, instance: DataInstance)) =>
        val field = lir.SubField(bundleRef, name, instance.tpe)
        lir.Assign(field, instance.refer)
    }

    val constructStmts = (stmts :+ bundleWire) ++ assigns
    RunResult(constructStmts, instance)
  }

  def runConstructModule(construct: backend.ConstructModule)(implicit stack: StackFrame, ctx: FirrtlContext, global: GlobalData): RunResult = {
    val moduleName = construct.name match {
      case backend.Term.Variable(name, _) => stack.lock(name); stack.refer(name)
      case backend.Term.Temp(id, _) => stack.next(id)
    }

    val moduleRef = lir.Reference(moduleName.name, construct.tpe)
    val instance = ModuleInstance(construct.tpe, ModuleLocation.Sub(moduleRef))
    stack.append(moduleName, instance)

    // In order to connect between two indirect module communication,
    // this method add statements for connecting between two modules.
    // current module is also subject to communication.
    def buildIndirectAccessCond(interface: MethodContainer, fromName: String)(targetBuilder: (String, BackendType) => lir.Ref): (Option[lir.Invalid], Vector[lir.Stmt]) = {
      // this method make source wire's name
      // For example, if looking into submodule's parent module's interface,
      // name will be [submodule instance name] . [parent module instance name]_[name] like sub.parent_call_active
      def fromRef(name: String, tpe: BackendType): lir.SubField = lir.SubField(moduleRef, fromName + "_" + name, tpe)

      val fromActive = fromRef(interface.activeName, BackendType.boolTpe)
      val isUnitRet = interface.ret.tpe.symbol == Symbol.unit

      val assignOpt =
        if (isUnitRet) Option.empty
        else {
          val dst = fromRef(interface.retName, interface.retTpe)
          lir.Assign(dst, targetBuilder(interface.retName, interface.retTpe)).some
        }
      val retInvalid = assignOpt
        .map(_ => fromRef(interface.retName, interface.retTpe))
        .map(ref => lir.Invalid(ref))

      val params = interface.params.map { case (name, tpe) => targetBuilder(name, tpe) }.toVector
      val args = interface.params.map { case (name, tpe) => fromRef(name, tpe) }.toVector
      val connects = (params zip args).map { case (param, arg) => lir.Assign(param, arg) }
      val (activeLitNode, activeLitRef) = makeNode(lir.Literal(1, BackendType.boolTpe))
      val activate = lir.Assign(targetBuilder(interface.activeName, BackendType.boolTpe), activeLitRef)
      val conseq = (activate +: connects) ++ assignOpt
      val when = lir.When(fromActive, conseq, Vector.empty)

      (retInvalid, Vector(activeLitNode, when))
    }

    // For submodule's parent module
    // mod sub: Sub = Sub {
    //   parent:
    //     xxx: ABC   <-- Here
    //     yyy: DEF   <--
    val (parentStmtss, parentCondss) = construct.parents.map {
      case (fromName, expr) =>
        // `refer` means which module instance is passed?
        val RunResult(stmts, ModuleInstance(tpe, refer)) = runExpr(expr)
        val parents = ctx.interfaces(tpe).filter(_.label.symbol.hasFlag(Modifier.Parent))

        val targetName: (String, BackendType) => lir.Ref = refer match {
          case ModuleLocation.This => (name: String, tpe: BackendType) => lir.Reference(name, tpe)
          case ModuleLocation.Upper(target) => (name: String, tpe: BackendType) => lir.Reference(target + "_" + name, tpe)
          case _: ModuleLocation.Sub => throw new ImplementationErrorException("refer a sub module as a parent module")
        }

        val (invalids, stmtss) = parents.map(buildIndirectAccessCond(_, fromName)(targetName)).unzip

        (stmts ++ invalids.flatten, stmtss.flatten)
    }.unzip

    // For submodule's sibling module
    val (siblingStmtss, siblingCondss) = construct.siblings.map {
      case (fromName, expr) =>
        val RunResult(stmts, ModuleInstance(tpe, refer)) = runExpr(expr)
        val siblings = ctx.interfaces(tpe).filter(_.label.symbol.hasFlag(Modifier.Sibling))

        val target: (String, BackendType) => lir.Ref = refer match {
          case ModuleLocation.This => throw new ImplementationErrorException("refer this module as sibling module")
          case ModuleLocation.Sub(refer) => (name: String, tpe: BackendType) => lir.SubField(refer, name, tpe)
          case ModuleLocation.Upper(refer) => (name: String, tpe: BackendType) => lir.Reference(NameTemplate.concat(refer, name), tpe)
        }

        val (invalid, stmtss) = siblings.map(buildIndirectAccessCond(_, fromName)(target)).unzip

        (stmts ++ invalid.flatten, stmtss.flatten)
    }.unzip

    // Assign default values to submodule's input or sibling interfaces
    // default:
    //   active     = false
    //   parameters = undefined
    val inputInitss = ctx.interfaces(construct.tpe) // get interfaces an instantiated submodule has
      .filter(interface => interface.label.symbol.hasFlag(Modifier.Input) || interface.label.symbol.hasFlag(Modifier.Sibling))
      .map {
        interface =>
          // In order to make submodule's wire names,
          // use this method.
          def buildRef(name: String, tpe: BackendType): lir.SubField = lir.SubField(moduleRef, name, tpe)

          val activeRef = buildRef(interface.activeName, BackendType.boolTpe)
          val params = interface.params.map{ case (name, tpe) => buildRef(name, tpe) }.toVector

          val (activeOffNode, activeOffRef) = makeNode(lir.Literal(0, BackendType.boolTpe))
          val activeOff = lir.Assign(activeRef, activeOffRef)
          val paramInvalid = params.map(lir.Invalid.apply)

          Vector(activeOffNode, activeOff) ++ paramInvalid
      }

    val inputPortWithoutDefaultInits = ctx.inputs(construct.tpe)
      .filter(_.ret.isEmpty)
      .map { port =>
        val portRef = lir.SubField(moduleRef, port.label.toString, port.tpe)
        val invalid = lir.Invalid(portRef)

        invalid
      }

    val inputPortWithDefaultInits = ctx.inputs(construct.tpe)
      .filter(_.ret.isDefined)
      .flatMap { port =>
        val portName = NameTemplate.portPrefix + port.label.toString
        val portTpe = port.tpe.copy(flag = port.tpe.flag | BackendTypeFlag.DefaultInput)
        val portRef = lir.SubField(moduleRef, portName, portTpe)
        val portActive = lir.SubField(portRef, NameTemplate.portActive, BackendType.boolTpe)
        val portBits = lir.SubField(portRef, NameTemplate.portBits, port.tpe)

        val (offNode, offLitRef) = makeNode(lir.Literal(0, BackendType.boolTpe))
        val activeOff = lir.Assign(portActive, offLitRef)
        val portInvalid = lir.Invalid(portBits)

        Vector(offNode, activeOff, portInvalid)
      }

    val inputPortInits = inputPortWithoutDefaultInits ++ inputPortWithDefaultInits
    val parentStmts = parentStmtss.toVector.flatten
    val siblingStmts = siblingStmtss.toVector.flatten
    val inputStmts = inputInitss.flatten
    val conds = (siblingCondss.toVector ++ parentCondss.toVector).flatten

    val stmts = inputPortInits ++ inputStmts ++ parentStmts ++ siblingStmts ++ conds

    RunResult(stmts, instance)
  }

  def runConstructMemory(memory: backend.ConstructMemory)(implicit stack: StackFrame, ctx: FirrtlContext, global: GlobalData): RunResult = {
    val refer = memory.name match {
      case backend.Term.Variable(name, _) => lir.Reference(name, memory.tpe)
      case backend.Term.Temp(id, _) => lir.Reference(stack.refer(id).name, memory.tpe)
    }

    val instance = ModuleInstance(memory.tpe, ModuleLocation.Sub(refer))

    RunResult(Vector.empty, instance)
  }

  def runConstructEnum(enum: backend.ConstructEnum)(implicit stack: StackFrame, ctx: FirrtlContext, global: GlobalData): RunResult = {
    def makeLeafs(tpe: BackendType, refer: lir.Ref): Vector[lir.Ref] = {
      tpe.symbol match {
        case _ if tpe.flag.hasFlag(BackendTypeFlag.Pointer) => Vector(refer)
        case sym if sym == Symbol.vec =>
          val HPElem.Num(length) = tpe.hargs.head
          val elemTpe = tpe.targs.head
          (0 until length).flatMap(idx => makeLeafs(elemTpe, lir.SubIndex(refer, idx, elemTpe))).toVector
        case sym if Symbol.isPrimitive(sym) => Vector(refer)
        case sym if sym.isEnumSymbol =>
          val dataRef = lir.SubField(refer, NameTemplate.enumData, tpe.copy(flag = tpe.flag | BackendTypeFlag.EnumData))
          val memberRef = lir.SubField(refer, NameTemplate.enumFlag, tpe.copy(flag = tpe.flag | BackendTypeFlag.EnumFlag))

          Vector(memberRef, dataRef)
        case _ =>
          val fields = tpe.fields.toVector.sortWith{ case ((left, _), (right, _)) => left < right }
          fields.flatMap { case (name, fieldTpe) =>
            val refField = lir.SubField(refer, name, fieldTpe)
            makeLeafs(fieldTpe, refField)
          }
      }
    }

    val insts = enum.passed.map(temp => stack.lookup(stack.refer(temp.id)))
    val temporaryNodes = Vector.newBuilder[lir.Node]
    val values = insts
      .map(_.asInstanceOf[DataInstance])
      .flatMap(inst => makeLeafs(inst.tpe, inst.refer))

    val concatOpt =
      if(values.isEmpty) None
      else lir.Concat(values, enum.tpe.copy(flag = enum.tpe.flag | BackendTypeFlag.EnumData)).some

    val variants = enum.tpe.symbol.tpe.declares
      .toMap.toVector
      .sortWith { case ((left, _), (right, _)) => left < right }
      .map { case (_, symbol) => symbol }
      .map(_.asEnumMemberSymbol)
    val variantMax = variants.map(_.memberID).max
    val variantWidth = atLeastLength(variantMax.toInt)
    val flagValue = lir.Literal(enum.variant.memberID, BackendType.bitTpe(variantWidth))
    val (flagNode, flagRef) = makeNode(flagValue)

    val enumName = stack.next("_ENUM")
    val enumRef = lir.Reference(enumName.name, enum.tpe)
    val wireDef = lir.Wire(enumName.name, enum.tpe)

    val memberTpe = enum.tpe.copy(flag = enum.tpe.flag | BackendTypeFlag.EnumFlag)
    val connectFlag = lir.Assign(
      lir.SubField(enumRef, "_member", memberTpe),
      flagRef
    )

    val dataTpe = enum.tpe.copy(flag = enum.tpe.flag | BackendTypeFlag.EnumData)
    val dataInvalid = lir.Invalid(lir.SubField(enumRef, "_data", dataTpe))
    val concatPairOpt = concatOpt.map(makeNode)
    val concatNodeOpt = concatPairOpt.map(_._1)
    val concatRefOpt = concatPairOpt.map(_._2)
    val connectDataOpt = concatRefOpt.map{ ref =>
      lir.Assign(
        lir.SubField(enumRef, "_data", dataTpe),
        ref
      )
    }

    val flagStmts = Vector(flagNode, connectFlag)
    val dataStmts = dataInvalid +: Vector(concatNodeOpt, connectDataOpt).flatten
    val runResultStmts = wireDef +: (temporaryNodes.result() ++ flagStmts ++ dataStmts)
    val instance = DataInstance(enum.tpe, enumRef)

    RunResult(runResultStmts, instance)
  }

  def runFinish(finish: backend.Finish)(implicit stack: StackFrame, ctx: FirrtlContext, global: GlobalData): RunResult = {
    val active = finish.stage.activeName
    val activeRef = lir.Reference(active, BackendType.boolTpe)
    val (literalNode, literalRef) = makeNode(lir.Literal(0, BackendType.boolTpe))
    val finishStmt = lir.Assign(activeRef, literalRef)
    val RunResult(unitStmts, unit) = DataInstance.unit()

    RunResult(Vector(literalNode, finishStmt) ++ unitStmts, unit)
  }

  def runGoto(goto: backend.Goto)(implicit stack: StackFrame, ctx: FirrtlContext, global: GlobalData): RunResult = {
    val stage = goto.state.label.stage
    val state = goto.state.label
    val stageContainer = ctx.stages(stack.lookupThis.get.tpe).find(_.label == stage).get
    val stateContainer = stageContainer.states.find(_.label == state).get
    val stateWidth = atLeastLength(stageContainer.states.length).toInt
    val stateTpe = BackendType.bitTpe(stateWidth)

    val stateRef = lir.Reference(stage.stateName, stateTpe)
    val (literalNode, literalRef) = makeNode(lir.Literal(state.index, stateTpe))
    val changeState = lir.Assign(stateRef, literalRef)

    val stmts = assignRegParams(stateContainer.params, goto.state.args, hasPriority = false)
    val RunResult(unitStmts, unitInstance) = DataInstance.unit()

    RunResult(Vector(literalNode, changeState) ++ stmts ++ unitStmts, unitInstance)
  }

  def runGenerate(generate: backend.Generate)(implicit stack: StackFrame, ctx: FirrtlContext, global: GlobalData): RunResult = {
    val stageContainer = ctx.stages(stack.lookupThis.get.tpe).find(_.label == generate.stage).get
    val activeRef = lir.Reference(generate.stage.activeName, BackendType.boolTpe)
    val (literalNode, literalRef) = makeNode(lir.Literal(1, BackendType.boolTpe))
    val activeViaName = stack.next("_GEN")
    val activate = lir.PriorityAssign(activeRef, activeViaName.name, literalRef)

    val (state, node) = generate.state match {
      case None => (None, None)
      case Some(backend.State(label, _)) =>
        val stateWidth = atLeastLength(stageContainer.states.length).toInt
        val stateTpe = BackendType.bitTpe(stateWidth)
        val stateRef = lir.Reference(stageContainer.label.stateName, stateTpe)
        val (stateValNode, stateValRef) = makeNode(lir.Literal(label.index, stateTpe))
        val via = stack.next("_GEN").name

        (lir.PriorityAssign(stateRef, via, stateValRef).some, stateValNode.some)
    }

    val stageAssigns = assignRegParams(stageContainer.params, generate.args, hasPriority = true)
    val stateAssigns = generate.state.map {
      state =>
        val backend.State(stateLabel, args) = state
        val stateContainer = stageContainer.states.find(_.label.index == stateLabel.index).get

        assignRegParams(stateContainer.params, args, hasPriority = true)
    }.getOrElse(Vector.empty)

    val stmts = Vector(literalNode, activate) ++ (node.toVector ++ state.toVector ++ stageAssigns ++ stateAssigns)
    val RunResult(unitStmts, unit) = DataInstance.unit()

    RunResult(stmts ++ unitStmts, unit)
  }

  private def assignRegParams(params: ListMap[String, BackendType], args: Vector[backend.Term.Temp], hasPriority: Boolean)(implicit stack: StackFrame, ctx: FirrtlContext, global: GlobalData): Vector[lir.Stmt] = {
    val instances = args.map{ case backend.Term.Temp(id, _) => stack.refer(id) }.map(stack.lookup).map(_.asInstanceOf[DataInstance])
    val paramRefs = params.map{ case (name, tpe) => lir.Reference(name, tpe) }

    (paramRefs zip instances).toVector.map{
      case (p, a) =>
        if(hasPriority) {
          val via = stack.next("_GEN").name
          lir.PriorityAssign(p, via, a.refer)
        } else {
          lir.Assign(p, a.refer)
        }
    }
  }

  def runReturn(ret: backend.Return)(implicit stack: StackFrame, ctx: FirrtlContext, global: GlobalData): RunResult = {
    val RunResult(stmts, instance) = runExpr(ret.expr)

    val disableLit = lir.Literal(0, BackendType.boolTpe)
    val disableNode = lir.Node(stack.next("_GEN").name, disableLit, BackendType.boolTpe)
    val disableRef = lir.Reference(disableNode.name, disableNode.tpe)
    val activeRef = lir.Reference(ret.blk.activeName, BackendType.boolTpe)
    val disableAssign = lir.Assign(activeRef, disableRef)
    val disableStmts = Vector(disableNode, disableAssign)

    val DataInstance(_, refer) = instance
    val idName = ret.blk.idName
    val retStmt = lir.Return(ret.proc.symbol.path, refer, Some(idName))
    val RunResult(unitStmts, unit) = DataInstance.unit()

    val headStmts = stmts ++ disableStmts
    RunResult((headStmts :+ retStmt) ++ unitStmts, unit)
  }

  def runCommence(commence: backend.Commence)(implicit stack: StackFrame, ctx: FirrtlContext, global: GlobalData): RunResult = {
    val stmts = activateProcBlock(commence.procLabel, commence.blkLabel, commence.args, fromInner = false)

    // Because there is no type field in ProcLabel, using &Bool as a alternative
    val pointer = BackendType.boolTpe.copy(flag = BackendTypeFlag.Pointer)

    val idRef = lir.Reference(commence.blkLabel.idName, pointer)
    val (stepIDNode, stepIDRef) = makeNode(lir.ProcStepID(commence.procLabel.toString, commence.blkLabel.symbol.name, pointer))
    val via = stack.next("_GEN").name
    val id = lir.PriorityAssign(idRef, via, stepIDRef)
    val idStmts = Vector(stepIDNode, id)

    val com = lir.Commence(commence.procLabel.symbol.path, commence.blkLabel.symbol.name, commence.tpe)
    val (commenceNode, commenceRef) = makeNode(com)
    val inst = DataInstance(commence.tpe, commenceRef)

    RunResult((stmts ++ idStmts) :+ commenceNode, inst)
  }

  def runRelayBlock(relay: backend.RelayBlock)(implicit stack: StackFrame, ctx: FirrtlContext, global: GlobalData): RunResult = {
    val RunResult(unitStmts, unit) = DataInstance.unit()
    val passID = lir.PassID(relay.dstBlk.idName, relay.srcBlk.idName)
    val srcActiveRef = lir.Reference(relay.srcBlk.activeName, BackendType.bitTpe(1))
    val disableLit = lir.Literal(0, BackendType.bitTpe(1))
    val disableNode = lir.Node(stack.next("_GEN").name, disableLit, disableLit.tpe)
    val disableRef = lir.Reference(disableNode.name, disableNode.tpe)
    val disableBlock = lir.Assign(srcActiveRef, disableRef)

    val headStmts = Vector(passID, disableNode, disableBlock)
    RunResult(
      headStmts ++ activateProcBlock(relay.procLabel, relay.dstBlk, relay.args, fromInner = true) ++ unitStmts,
      unit
    )
  }

  def runDeref(deref: backend.Deref)(implicit stack: StackFrame, ctx: FirrtlContext, global: GlobalData): RunResult = {
    val name = stack.refer(deref.id.id)
    val instance = stack.lookup(name).asInstanceOf[DataInstance]
    val ref = instance.refer.asInstanceOf[lir.Reference]
    val srcTpe = instance.tpe

    val tpe = BackendType(BackendTypeFlag.NoFlag, srcTpe.symbol, srcTpe.hargs, srcTpe.targs)
    val refName = stack.next("_GEN")
    val stmt  = lir.Deref(refName.name, ref, tpe)
    val refer = lir.Reference(refName.name, tpe)
    val inst = DataInstance(tpe, refer)

    RunResult(Vector(stmt), inst)
  }

  def activateProcBlock(procLabel: ProcLabel, blkLabel: ProcBlockLabel, args: Vector[backend.Term.Temp], fromInner: Boolean)(implicit stack: StackFrame, ctx: FirrtlContext, global: GlobalData): Vector[lir.Stmt] = {
    def assignStmtGen(dst: lir.Ref, src: lir.Ref): lir.Stmt = {
      if(fromInner) lir.Assign(dst, src)
      else {
        val via = stack.next("_GEN").name
        lir.PriorityAssign(dst, via, src)
      }
    }

    val procContainer = ctx.procs(stack.lookupThis.get.tpe).find(_.label == procLabel).get
    val activeRef = lir.Reference(blkLabel.activeName, BackendType.boolTpe)
    val (litNode, litRef) = makeNode(lir.Literal(1, BackendType.boolTpe))
    val activate = assignStmtGen(activeRef, litRef)

    val blkContainer = procContainer.blks.find(_.label == blkLabel).get
    val assigns = (blkContainer.params.toVector zip args).map {
      case ((param, tpe), arg) =>
        val paramRef = lir.Reference(param, tpe)
        val argRef = lir.Reference(stack.refer(arg.id).name, tpe)
        assignStmtGen(paramRef, argRef)
    }

    Vector(litNode, activate) ++ assigns
  }

  /*
  private def definition[A <: ir.FirrtlNode, B <: ir.FirrtlNode](normalBuilder: (String, ir.Type) => A)(name: String, tpe: BackendType)(implicit global: GlobalData): Option[A] = {
    val normalComponent = Option(tpe)
      .filter(_.symbol != Symbol.unit)
      .map(tpe => toFirrtlType(tpe))
      .map(tpe => normalBuilder(name, tpe))

    normalComponent
  }

  private def wire(name: String, tpe: BackendType)(implicit global: GlobalData): Option[ir.DefWire] = {
    val wireBuilder = (name: String, tpe: ir.Type) => ir.DefWire(ir.NoInfo, name, tpe)
    definition(wireBuilder)(name, tpe)
  }

  private def register(name: String, tpe: BackendType)(implicit global: GlobalData): Option[ir.DefRegister] = {
    val regBuilder = (name: String, tpe: ir.Type) => ir.DefRegister(ir.NoInfo, name, tpe, clockRef, resetRef, ir.Reference(name, ir.UnknownType))
    val wireBuilder = (name: String, tpe: ir.Type) => ir.DefWire(ir.NoInfo, name, tpe)

    definition(regBuilder)(name, tpe)
  }

  private def port(name: String, tpe: BackendType, flow: ir.Direction)(implicit global: GlobalData): Option[ir.Port] = {
    val portBuilder = (name: String, tpe: ir.Type) => ir.Port(ir.NoInfo, name, flow, tpe)

    definition(portBuilder)(name, tpe)
  }
  */

  private def makeNode(expr: lir.Expr)(implicit stack: StackFrame): (lir.Node, lir.Reference) = {
    val node = lir.Node(
      stack.next("_GEN").name,
      expr,
      expr.tpe
    )
    val ref = lir.Reference(node.name, expr.tpe)

    (node, ref)
  }

  private def removeUnitNode(stmts: Vector[lir.Stmt])(implicit globa: GlobalData): Vector[lir.Stmt] = {
    val unitTpe = toBackendType(Type.unitTpe)
    val (_, removed) = stmts.collectPartition{ case n @ lir.Node(_, _, tpe) if tpe == unitTpe => n }

    removed
  }
}
