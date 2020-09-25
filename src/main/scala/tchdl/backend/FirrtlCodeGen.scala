package tchdl.backend

import tchdl.backend.{ast => backend}
import tchdl.backend.ast.{BackendLIR => lir}
import tchdl.util._
import tchdl.util.TchdlException._

import firrtl.PrimOps
import scala.annotation.tailrec
import scala.collection.immutable.ListMap
import scala.collection.mutable

object FirrtlCodeGen {
  case class BuildResult[T](stmts: Vector[lir.Stmt], component: T)
  case class FirrtlContext(
    interfaces: Map[BackendType, Vector[MethodContainer]],
    stages: Map[BackendType, Vector[StageContainer]],
    procs: Map[BackendType, Vector[ProcContainer]],
    methods: Map[BackendType, Vector[MethodContainer]],
    functions: Vector[MethodContainer]
  )

  abstract class StackFrame {
    protected def parent: StackFrame

    private val scope: mutable.Map[Name, Instance] = mutable.Map.empty
    protected val namer: FirrtlNamer
    val lookupThis: Option[Instance]

    def next(name: String): Name = {
      namer.variable.next(name)

      if (parent != null)
        parent.count(name)

      refer(name)
    }

    def next(id: Int): Name = {
      namer.temp.next(id)

      if (parent != null)
        parent.count(id)

      refer(id)
    }

    def refer(name: String): Name = namer.variable.refer(name)
    def refer(id: Int): Name = namer.temp.refer(id)

    def lock(name: String): Unit = namer.variable.lock(name)

    @tailrec private def count(name: String): Unit = {
      namer.variable.count(name)

      if (parent != null)
        parent.count(name)
    }

    @tailrec private def count(id: Int): Unit = {
      namer.temp.count(id)

      if (parent != null)
        parent.count(id)
    }

    def lookup(name: Name): Instance = scope.get(name) match {
      case Some(instance) => instance
      case None => throw new ImplementationErrorException("instance must be there")
    }

    def append(name: Name, instance: Instance): Unit = {
      scope(name) = instance
    }
  }

  object StackFrame {
    def apply(thisTerm: Instance): StackFrame = {
      new StackFrame {
        override val namer = new FirrtlNamer
        override val parent = null
        override val lookupThis = Some(thisTerm)
      }
    }

    def apply(parent: StackFrame, thisTerm: Option[Instance]): StackFrame = {
      val _parent = parent

      new StackFrame {
        override val namer = _parent.namer.copy
        override val parent = _parent
        override val lookupThis = thisTerm
      }
    }
  }

  class FirrtlNamer {
    val temp: Counter[Int] = new TempCounter
    val variable: Counter[String] = new VariableCounter

    def copy: FirrtlNamer = {
      val _temp = this.temp.copy
      val _variable = this.variable.copy

      new FirrtlNamer {
        override val temp = _temp
        override val variable = _variable
      }
    }
  }

  abstract class Counter[T] {
    protected val table: mutable.Map[T, Int] = mutable.Map.empty

    def next(key: T): Name
    def count(key: T): Unit
    def refer(key: T): Name
    def lock(key: T): Unit
    def copy: Counter[T]
  }

  class TempCounter extends Counter[Int] {
    protected var max = 0

    def next(key: Int): Name = {
      val nextMax = max + 1
      table(key) = nextMax
      max = nextMax

      Name(s"_TEMP_$nextMax")
    }

    def count(key: Int): Unit = {
      max = max + 1
    }

    def refer(key: Int): Name = {
      val value = table(key)
      Name(s"_TEMP_$value")
    }

    def lock(key: Int): Unit = throw new ImplementationErrorException("lock is not allowed to temp counter")

    def copy: Counter[Int] = {
      val _max = this.max
      val _table = this.table.clone()

      new TempCounter {
        max = _max
        override protected val table: mutable.Map[Int, Int] = _table
      }
    }
  }

  class VariableCounter extends Counter[String] {
    protected val eachMax = mutable.Map.empty[String, Int]
    private val locked = mutable.Set.empty[String]

    def next(key: String): Name = {
      assert(!locked(key), s"[$key] is locked")

      eachMax.get(key) match {
        case Some(count) =>
          table(key) = count + 1
          eachMax(key) = count + 1
          Name(s"${key}_$count")
        case None =>
          table(key) = 0
          eachMax(key) = 0
          Name(s"${key}_0")
      }
    }

    def count(key: String): Unit = {
      eachMax.get(key) match {
        case Some(count) => eachMax(key) = count + 1
        case None if locked(key) => // nothing to do
        case None => eachMax(key) = 0
      }
    }

    def refer(key: String): Name = {
      table.get(key) match {
        case Some(count) => Name(s"${key}_$count")
        case None if locked(key) => Name(key)
        case None => throw new ImplementationErrorException(s"there is no count or lock for [$key]")
      }
    }

    def lock(key: String): Unit = {
      locked += key
    }

    def copy: Counter[String] = {
      val _table = this.table.clone()
      val _eachMax = this.eachMax.clone()

      new VariableCounter {
        override protected val table: mutable.Map[String, Int] = _table
        override protected val eachMax: mutable.Map[String, Int] = _eachMax
      }
    }
  }

  def exec(modules: Vector[ModuleContainer], methods: Vector[MethodContainer])(implicit global: GlobalData): Vector[lir.Module] = {
    val interfaceTable = modules.map(module => module.tpe -> module.bodies.flatMap(_.interfaces)).toMap
    val stageTable = modules.map(module => module.tpe -> module.bodies.flatMap(_.stages)).toMap
    val procTable = modules.map(module => module.tpe -> module.bodies.flatMap(_.procs)).toMap
    val methodTable = methods
      .collect { case method if method.label.accessor.isDefined => method }
      .groupBy(_.label.accessor.get)
    val functionTable = methods.collect { case method if method.label.accessor.isEmpty => method }
    val context = FirrtlContext(
      interfaceTable,
      stageTable,
      procTable,
      methodTable,
      functionTable
    )

    modules.map(buildModule(_, context))
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
    val stageSigs = module.stages.map(buildStageSignature(_)(stack, ctx, global))

    val ports = inputs.map(_.component) ++ outputs.map(_.component) ++ inputInterfaces.flatMap(_.component)
    val components = internals.map(_.component) ++ registers.map(_.component) ++ normalInterfaces.flatMap(_.component) ++ stageSigs.flatMap(_.component)
    val (instances, accessCondss) = modules.map(_.component).unzip
    val mems = memories.map(_.component)

    val interfaceInits = inputs.flatMap(_.stmts) ++ outputs.flatMap(_.stmts) ++ internals.flatMap(_.stmts)
    val componentInits = registers.flatMap(_.stmts) ++ modules.flatMap(_.stmts) ++ memories.flatMap(_.stmts) ++ inputInterfaces.flatMap(_.stmts) ++ normalInterfaces.flatMap(_.stmts) ++ stageSigs.flatMap(_.stmts)
    val inits = interfaceInits ++ componentInits

    val interfaceBodies = module.interfaces.map(runInterface(_)(stack, ctx, global))
    val alwayss = module.always.map(runAlways(_)(stack, ctx, global))
    val stageBodies = module.stages.map(runStage(_)(stack, ctx, global))
    val procedures = accessCondss.flatten ++ interfaceBodies.map(_.component) ++ stageBodies.map(_.component) ++ alwayss.flatMap(_.stmts)

    lir.Module(tpe, ports, instances, mems, hpStmts ++ components, inits, procedures)
  }

  def runInput(field: FieldContainer)(implicit stack: StackFrame, ctx: FirrtlContext, global: GlobalData): BuildResult[lir.Port] = {
    val stmts = field.code.flatMap(runStmt)
    val retExpr = field.ret.map(throw new ImplementationErrorException("input wire with init expression is not supported yet"))
    val port = lir.Port(lir.Dir.Input, field.toFirrtlString, field.tpe)

    BuildResult(stmts, port)
  }

  def runOutput(field: FieldContainer)(implicit stack: StackFrame, ctx: FirrtlContext, global: GlobalData): BuildResult[lir.Port] = {
    val stmts = field.code.flatMap(runStmt)
    val fieldRef = lir.Reference(field.toFirrtlString, field.tpe)
    val retStmt = field.ret.map(runExpr) match {
      case None => Vector.empty
      case Some(RunResult(stmts, inst: DataInstance)) =>
        val connectOpt = lir.Assign(fieldRef, inst.refer)
        stmts :+ connectOpt
    }

    val port = lir.Port(lir.Dir.Output, field.toFirrtlString, field.tpe)

    BuildResult(stmts ++ retStmt, port)
  }

  def runInternal(field: FieldContainer)(implicit stack: StackFrame, ctx: FirrtlContext, global: GlobalData): BuildResult[lir.Wire] = {
    val stmts = field.code.flatMap(runStmt)
    val retStmt = field.ret.map(runExpr) match {
      case None => Vector.empty
      case Some(RunResult(stmts, inst: DataInstance)) =>
        val fieldRef = lir.Reference(field.toFirrtlString, field.tpe)
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

    /*
    val memDef = ir.DefMemory(
      ir.NoInfo,
      memory.label.toString,
      dataType,
      depth,
      writeLatency,
      readLatency,
      (0 until readPort).map(idx => s"read$idx"),
      (0 until writePort).map(idx => s"write$idx"),
      Seq.empty,
      ir.ReadUnderWrite.Undefined
    )

    def memSubField(fields: String*): ir.Expression =
      fields.foldLeft[ir.Expression](ir.Reference(memory.toFirrtlString, ir.UnknownType)) {
        case (accessor, name) => ir.SubField(accessor, name, ir.UnknownType)
      }

    def buildWriteMaskInit(tpe: ir.Type, idx: Int): Vector[ir.Connect] = {
      def loop(fieldTpe: ir.Type, accessor: ir.SubField): Vector[ir.SubField] = {
        fieldTpe match {
          case ir.UIntType(_) => Vector(accessor.copy(tpe = ir.UIntType(ir.IntWidth(1))))
          case bundle: ir.BundleType =>
            bundle.fields.toVector.flatMap(
              field => loop(field.tpe, ir.SubField(accessor, field.name, ir.UnknownType))
            )
        }
      }

      val port = s"write$idx"
      val subField = memSubField(port, "mask").asInstanceOf[ir.SubField]
      val leafs = tpe match {
        case ir.UIntType(_) => Vector(subField.copy(tpe = ir.UIntType(ir.IntWidth(1))))
        case bundle: ir.BundleType => loop(bundle, subField)
      }

      leafs.map(loc => ir.Connect(ir.NoInfo, loc, ir.UIntLiteral(0)))
    }

    def buildReadStmts(idx: Int): Vector[ir.Statement] = {
      val readFlagRegNames = (0 until readLatency).map(latency => memory.label.toString + "$" + s"_reading${latency}_$idx").toVector
      val readFlagRegs = readFlagRegNames.map(ir.DefRegister(ir.NoInfo, _, ir.UIntType(ir.IntWidth(1)), clockRef, resetRef, ir.UIntLiteral(0)))
      val readingRegDefault = readFlagRegNames.headOption.map(name => ir.Connect(ir.NoInfo, ir.Reference(name, ir.UnknownType), ir.UIntLiteral(0)))
      val port = s"read$idx"
      val readEnable = ir.Connect(ir.NoInfo, memSubField(port, "en"), ir.UIntLiteral(0))
      val readAddr = ir.IsInvalid(ir.NoInfo, memSubField(port, "addr"))
      val readClk = ir.Connect(ir.NoInfo, memSubField(port, "clk"), clockRef)

      val readDataName = memory.toFirrtlString + "$" + s"_${port}_data"
      val readDataFuture = ir.BundleType(Seq(
        ir.Field("_member", ir.Default, ir.UIntType(ir.IntWidth(1))),
        ir.Field("_data", ir.Default, dataType)
      ))

      val readDataWire = ir.DefWire(ir.NoInfo, readDataName, readDataFuture)
      def memberConnect(from: ir.Expression): ir.Connect = ir.Connect(
        ir.NoInfo,
        ir.SubField(ir.Reference(readDataName, ir.UnknownType), "_member", ir.UnknownType),
        from
      )

      val readingRegConnects = readFlagRegNames match {
        case Vector() => Vector.empty
        case names => (names zip names.tail).map{
          case (from, loc) =>
            val fromRef = ir.Reference(from, ir.UnknownType)
            val locRef = ir.Reference(loc, ir.UnknownType)

            ir.Connect(ir.NoInfo, locRef, fromRef)
        }
      }

      val readDataMemberConnect = readFlagRegNames.lastOption match {
        case None => memberConnect(ir.UIntLiteral(0))
        case Some(name) => memberConnect(ir.Reference(name, ir.UnknownType))
      }

      val readDataDataConnect = ir.Connect(
        ir.NoInfo,
        ir.SubField(ir.Reference(readDataName, ir.UnknownType), "_data", ir.UnknownType),
        memSubField(port, "data")
      )

      val stmts = Vector(readEnable, readAddr, readClk, readDataWire)
      val connects = Vector(readDataMemberConnect, readDataDataConnect)

      readFlagRegs ++ readingRegDefault ++ stmts ++ readingRegConnects ++ connects
    }

    def buildWriteStmts(idx: Int): Vector[ir.Statement] = {
      val port = s"write$idx"

      val writeMask = buildWriteMaskInit(dataType, idx)
      val writeEnable = ir.Connect(ir.NoInfo, memSubField(port, "en"), ir.UIntLiteral(0))
      val writeAddr = ir.IsInvalid(ir.NoInfo, memSubField(port, "addr"))
      val writeData = ir.IsInvalid(ir.NoInfo, memSubField(port, "data"))
      val writeClk = ir.Connect(ir.NoInfo, memSubField(port, "clk"), clockRef)

      writeMask ++ Vector(writeEnable, writeAddr, writeData, writeClk)
    }

    val readStmts = (0 until readPort).flatMap(buildReadStmts).toVector
    val writeStmts = (0 until writePort).flatMap(buildWriteStmts).toVector

    BuildResult(memDef +: (readStmts ++ writeStmts), ())
    */
  }

  private def log2(x: Double): Double = math.log10(x) / math.log10(2.0)
  private def atLeastLength(x: Double): Double = {
    val width = (math.ceil _ compose log2) (x)
    if (width == 0) 1
    else width
  }

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
    val activeNode = lir.Node(stack.next("_GEN").name, lir.Literal(1, activeTpe), activeTpe)
    val activeRef = lir.Reference(activeNode.name, activeTpe)
    val active = lir.Reg(stage.activeName, Some(activeRef), activeTpe)

    val stageRegs = buildParams(stage.params.toVector)
    val stateRegs = buildParams(stage.states.flatMap(_.params))

    val stateLen = atLeastLength(stage.states.length).toInt
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
    val states = stage.states.zipWithIndex.map {
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

        lir.When (condRef, stateStmts, Vector.empty)
    }

    val cond = lir.When(
      lir.Reference(stage.activeName, BackendType.boolTpe),
      stmts ++ states,
      Vector.empty
    )

    BuildResult(Vector.empty, cond)
  }

  def buildProcSignature(proc: ProcContainer)(implicit stack: StackFrame, ctx: FirrtlContext, global: GlobalData): Vector[lir.Stmt] = {
    val params = proc.blks.flatMap(_.params.toVector)
    val regs = params.map{ case (name, tpe) => lir.Reg(name, Option.empty, tpe) }
    val wire = lir.Wire(proc.label.retName, proc.ret)

    // add instances to stack
    params.foreach { case (name, _) => stack.lock(name) }
    val instances = params.map { case (name, tpe) => StructInstance(tpe, lir.Reference(name, tpe)) }
    (params zip instances).foreach{ case ((name, _), inst) => stack.append(Name(name), inst) }

    val activeOff = lir.Literal(0, BackendType.boolTpe)
    val (activeOffNode, activeOffRef) = makeNode(activeOff)
    val blkActives = proc.blks
      .map(_.label.activeName)
      .map(name => lir.Reg(name, activeOffRef.some, BackendType.boolTpe))

    (regs :+ activeOffNode) ++ (blkActives :+ wire)
  }

  def runProc(proc: ProcContainer)(implicit stack: StackFrame, ctx: FirrtlContext, global: GlobalData): BuildResult[Vector[lir.When]] = {
    val retName = proc.label.retName

    // for default expression
    val stmts = proc.default.flatMap(runStmt)
    val RunResult(exprStmts, defaultInst: DataInstance) = runExpr(proc.defaultRet)
    val defaultAssign = lir.Assign(lir.Reference(retName, proc.ret), defaultInst.refer)
    val defaultStmts = stmts ++ exprStmts :+ defaultAssign

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

    val retRef = retName.map(lir.Reference(_, interface.retTpe))
    val retInvalid = retName.map(name => lir.Invalid(name))
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
    val invalids = wireRefs.map(ref => lir.Invalid(ref.name))

    val wires = active +: sigWires
    val inits = Vector(activeOffNode, activeOff) ++ invalids

    BuildResult(inits, wires)
  }

  def runInterface(interface: MethodContainer)(implicit stack: StackFrame, ctx: FirrtlContext, global: GlobalData): BuildResult[lir.When] = {
    val stmts = interface.code.flatMap(runStmt(_))
    val RunResult(retStmts, instance: DataInstance) = runExpr(interface.ret)
    val methodRetTpe = interface.label.symbol.tpe.asMethodType.returnType
    val retConnect =
      if (methodRetTpe == Type.unitTpe) Option.empty
      else lir.Assign(lir.Reference(interface.retName, interface.retTpe), instance.refer).some

    val activeRef = lir.Reference(interface.activeName, BackendType.boolTpe)
    val literal = lir.Literal(1, BackendType.boolTpe)
    val (literalNode, literalRef) = makeNode(literal)
    val (opsNode, opsRef) = makeNode(lir.Ops(PrimOps.Eq, Vector(activeRef, literalRef), Vector.empty, BackendType.boolTpe))

    val cond = lir.When(opsRef, stmts ++ retStmts ++ retConnect, Vector.empty)

    BuildResult(Vector(literalNode, opsNode), cond)
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
        val paramInits = params.map(param => lir.Invalid(param.name))

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
      case Some(tpe) => ctx.methods(tpe).find(_.label == call.label).get
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

    val newStack = StackFrame(stack, accessor)

    val hargNames = method.hparams.keys.map(newStack.next)
    val argNames = method.params.keys.map(newStack.next)

    (hargNames zip hargs).foreach { case (name, harg) => newStack.append(name, harg) }
    (argNames zip args).foreach { case (name, arg) => newStack.append(name, arg) }

    val stmts = method.code.flatMap(stmt => runStmt(stmt)(newStack, ctx, global))
    val RunResult(retStmts, instance) = runExpr(method.ret)(newStack, ctx, global)

    RunResult(hargStmts ++ stmts ++ retStmts, instance)
  }

  def runCallInterface(call: backend.CallInterface)(implicit stack: StackFrame, ctx: FirrtlContext, global: GlobalData): RunResult = {
    /*
    def callInternal(tpe: BackendType): RunResult = {
      val candidates = ctx.interfaces(tpe)
      val interface = candidates.find(_.label == call.label).get

      val paramRefs = interface.params
        .map { case (name, _) => stack.refer(name) }
        .map { name => ir.Reference(name.name, ir.UnknownType) }

      val argNames = call.args.map {
        case backend.Term.Temp(id, _) => stack.refer(id)
        case backend.Term.Variable(name, _) => stack.refer(name)
      }
      val argInstances = argNames.map(stack.lookup).map(_.asInstanceOf[DataInstance])

      val (futures, connectOpts) = (paramRefs zip argInstances).map{ case (p, a) => connect(p, a) }.unzip
      val future = futures.foldLeft(Future.empty)(_ + _)
      val connects = connectOpts.flatten.toVector
      val activate = ir.Connect(ir.NoInfo, ir.Reference(interface.activeName, ir.UnknownType), ir.UIntLiteral(1))
      val returnedInstance = interface.ret match {
        case backend.UnitLiteral() => DataInstance()
        case _ => DataInstance(interface.retTpe, ir.Reference(interface.retName, ir.UnknownType))
      }

      RunResult(future, activate +: connects, returnedInstance)
    }

    def callToSubModule(module: ir.Reference, tpe: BackendType): RunResult = {
      val candidates = ctx.interfaces(tpe)
      val interface = candidates.find(_.label == call.label).get

      val params = interface.params.toVector.map { case (name, _) => ir.SubField(module, name, ir.UnknownType) }
      val argNames = call.args.map {
        case backend.Term.Temp(id, _) => stack.refer(id)
        case backend.Term.Variable(name, _) => stack.refer(name)
      }
      val args = argNames.map(stack.lookup).map(_.asInstanceOf[DataInstance])
      val activate = ir.Connect(ir.NoInfo, ir.SubField(module, interface.activeName, ir.UnknownType), ir.UIntLiteral(1))

      val (futures, connectOpts) = (params zip args).map{ case (p, a) => connect(p, a) }.unzip
      val connects = connectOpts.flatten
      val future = futures.foldLeft(Future.empty)(_ + _)

      val returnedInstance = interface.ret match {
        case backend.UnitLiteral() => DataInstance()
        case _ => DataInstance(interface.retTpe, ir.SubField(module, interface.retName, ir.UnknownType))
      }

      RunResult(future, activate +: connects, returnedInstance)
    }

    def callToUpperModule(module: String, tpe: BackendType): RunResult = {
      def refBuilder(name: String): ir.Reference = ir.Reference(module + "$" + name, ir.UnknownType)

      val candidates = ctx.interfaces(tpe)
      val interface = candidates.find(_.label == call.label).get
      val params = interface.params.toVector.map { case (name, _) => refBuilder(name) }

      val argNames = call.args.map {
        case backend.Term.Temp(id, _) => stack.refer(id)
        case backend.Term.Variable(name, _) => stack.refer(name)
      }
      val args = argNames.map(stack.lookup).map(_.asInstanceOf[DataInstance])

      val activate = ir.Connect(ir.NoInfo, refBuilder(interface.activeName), ir.UIntLiteral(1))
      val (futures, connectOpts) = (params zip args).map{ case (p, a) => connect(p, a) }.unzip
      val future = futures.foldLeft(Future.empty)(_ + _)
      val connects = connectOpts.flatten
      val returnedInstance = interface.ret match {
        case backend.UnitLiteral() => DataInstance()
        case _ => DataInstance(interface.retTpe, refBuilder(interface.retName))
      }

      RunResult(future, activate +: connects, returnedInstance)
    }
    */

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
      case "orBool"  => builtin.boolOr(insts(0), insts(1))
      case "andBool" => builtin.boolAnd(insts(0), insts(1))
      case "xorBool" => builtin.boolXor(insts(0), insts(1))
      case "eqBool" => builtin.boolEq(insts(0), insts(1), global)
      case "neBool" => builtin.boolNe(insts(0), insts(1), global)
      case "notBool" => builtin.boolNot(insts(0), stack, global)
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

  def runReadMemory(read: backend.ReadMemory)(implicit stack: StackFrame, ctx: FirrtlContext, global: GlobalData): RunResult = {
    def getName(term: backend.Term): Name = term match {
      case backend.Term.Variable(name, _) => stack.refer(name)
      case backend.Term.Temp(id, _) => stack.refer(id)
    }

    val ModuleInstance(_, location) = stack.lookup(getName(read.accessor))
    val ModuleLocation.Sub(memory @ lir.Reference(memName, _)) = location
    val DataInstance(_, addrRef) = stack.lookup(getName(read.addr))

    val readTpe = read.tpe.copy(isPointer = true)
    val readStmt = lir.MemRead(memName, read.port, addrRef, readTpe)
    val readDataRef = lir.Reference(memName + "_" + s"_${read.port}_data", readTpe)
    val instance = DataInstance(readTpe, readDataRef)

    RunResult(Vector(readStmt), instance)
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
    def extractFieldData(source: lir.SubField, tpe: BackendType, bitIdx: BigInt): (Vector[lir.Stmt], Name, BigInt) = {
      /*
      tpe match {
        case UIntType(firrtl.ir.IntWidth(width)) =>
          val name = stack.next("_EXTRACT")
          val tpe = BackendType.bitTpe(width.toInt)
          val expr = lir.Ops(PrimOps.Bits, Vector(source), Vector(bitIdx + width - 1, bitIdx), tpe)
          val node = lir.Node(name.name, expr, expr.tpe)

          (Vector(node), name, bitIdx + width)
        case BundleType(fields) =>
          val bundleName = stack.next("_EXTRACT")
          val wire = lir.Wire(bundleName.name, tpe)

          def subField(name: String): ir.SubField =
            ir.SubField(
              ir.Reference(bundleName.name, tpe),
              name,
              ir.UnknownType
            )

          val (stmts, nextIdx) = fields.foldLeft((Vector.empty[ir.Statement], bitIdx)) {
            case ((stmts, idx), field) =>
              val (leafStmts, name, nextIdx) = extractFieldData(source, field.tpe, idx)
              val connect = ir.Connect(ir.NoInfo, subField(field.name), ir.Reference(name.name, ir.UnknownType))

              (stmts ++ leafStmts :+ connect, nextIdx)
          }

          (wire +: stmts, bundleName, nextIdx)
        case VectorType(tpe, length) =>

      }
      */

      tpe.symbol match {
        case sym if sym == Symbol.bit =>
          val name = stack.next("_EXTRACT")
          val HPElem.Num(width) = tpe.hargs(0)
          val dataTpe = BackendType.bitTpe(width)
          val expr = lir.Ops(PrimOps.Bits, Vector(source), Vector(bitIdx + width - 1, bitIdx), dataTpe)
          val node = lir.Node(name.name, expr, dataTpe)

          (Vector(node), name, bitIdx + width)
        case sym if sym == Symbol.vec =>
          val vecName = stack.next("_EXTRACT")
          val wire = lir.Wire(vecName.name, tpe)
          val wireRef = lir.Reference(wire.name, wire.tpe)
          val HPElem.Num(length) = tpe.hargs(0)
          val elemTpe = tpe.targs(0)

          val (stmts, nextIdx) = (0 to length).foldLeft(Vector.empty[lir.Stmt], bitIdx){
            case ((stmts, bitIdx), idx) =>
              val (leafStmts, name, nextIdx) = extractFieldData(source, elemTpe, bitIdx)
              val assign = lir.Assign(
                lir.SubIndex(wireRef, idx, elemTpe),
                lir.Reference(name.name, elemTpe)
              )

              (stmts ++ leafStmts :+ assign, nextIdx)
          }

          (wire +: stmts, vecName, nextIdx)
        case _ =>
          val bundleName = stack.next("_EXTRACT")
          val wire = lir.Wire(bundleName.name, tpe)
          val fields = tpe.fields.toVector.sortWith{ case ((left, _), (right, _)) => left < right }

          val (stmts, nextIdx) = fields.foldLeft((Vector.empty[lir.Stmt], bitIdx)) {
            case ((stmts, idx), (name, fieldTpe)) =>
              val subField = lir.SubField(source, name, fieldTpe)
              val (leafStmts, extractName, nextIdx) = extractFieldData(subField, fieldTpe, idx)
              val dstField = lir.SubField(lir.Reference(bundleName.name, tpe), name, fieldTpe)
              val extractField = lir.Reference(extractName.name, fieldTpe)
              val assign = lir.Assign(dstField, extractField)

              (stmts ++ leafStmts :+ assign, nextIdx)
          }

          (wire +: stmts, bundleName, nextIdx)
      }
    }

    def runPattern(instance: DataInstance, pattern: backend.MatchPattern): RunResult = {
      def toLIRForm(lit: backend.Literal): lir.Literal = {
        def toLit(value: Int, width: Int): lir.Literal = lir.Literal(value, BackendType.bitTpe(width))

        lit match {
          case backend.IntLiteral(value) => toLit(value, 32)
          case backend.BitLiteral(value, HPElem.Num(width)) => toLit(value.toInt, width)
          case backend.BoolLiteral(value) => toLit(if(value) 1 else 0, 1)
          case backend.UnitLiteral() => toLit(0, 0)
        }
      }

      def literalPattern(lit: backend.Literal): RunResult = {
        val locName = stack.next("_GEN")
        val loc = lir.Reference(locName.name, lit.tpe)
        val locTpe = BackendType.boolTpe
        val literal = toLIRForm(lit)
        val (literalNode, literalRef) = makeNode(literal)
        val cmp = lir.Ops(PrimOps.Eq, Vector(instance.refer, literalRef), Vector.empty, BackendType.boolTpe)
        val node = lir.Node(locName.name, cmp, BackendType.boolTpe)
        val inst = DataInstance(locTpe, loc)

        RunResult(Vector(literalNode, node), inst)
      }

      def identPattern(variable: backend.Term.Variable): RunResult = {
        val locName = stack.next(variable.name)
        val loc = lir.Reference(locName.name, variable.tpe)
        val node = lir.Node(locName.name, instance.refer, variable.tpe)
        val locInstance = DataInstance(instance.tpe, loc)
        stack.append(locName, locInstance)
        val RunResult(stmts, inst: DataInstance) = DataInstance.bool(bool = true)

        RunResult(node +: stmts, inst)
      }

      pattern match {
        case backend.WildCardPattern(_) => DataInstance.bool(bool = true)
        case backend.LiteralPattern(lit) => literalPattern(lit)
        case backend.IdentPattern(name) => identPattern(name)
        case backend.EnumPattern(variant, patterns, tpe) =>
          // This may be the easiest way
          // At once, convert backend type into firrtl type
          // and extract each field's type, member's type and data's type.
          // Finally, reconverting each firrtl types into backend types
          val firrtlTpe = toFirrtlType(tpe).asInstanceOf[firrtl.ir.BundleType]

          val memberFirTpe = firrtlTpe.fields.find(_.name == "_member").map(_.tpe).get.asInstanceOf[firrtl.ir.UIntType]
          val memberWidth = memberFirTpe.width.asInstanceOf[firrtl.ir.IntWidth].width.toInt
          val memberTpe = BackendType.bitTpe(memberWidth)
          val memberRef = lir.SubField(instance.refer, "_member", memberTpe)

          val dataFirTpe = firrtlTpe.fields.find(_.name == "_data").map(_.tpe).get.asInstanceOf[firrtl.ir.UIntType]
          val dataTpe = BackendType.bitTpe(dataFirTpe.width.asInstanceOf[firrtl.ir.IntWidth].width.toInt)
          val dataRef = lir.SubField(instance.refer, "_data", dataTpe)

          val (litNode, litRef) = makeNode(lir.Literal(variant, memberTpe))
          val variantEq = lir.Ops(
            PrimOps.Eq,
            Vector(memberRef, litRef),
            Vector.empty,
            BackendType.boolTpe
          )

          val stmtBuilder = Vector.newBuilder[lir.Stmt]
          val refBuilder = Vector.newBuilder[lir.Reference]
          patterns.map(_.tpe).scanLeft(BigInt(0)) {
            case (idx, tpe) =>
              val (stmts, name, nextIdx) = extractFieldData(dataRef, tpe, idx)
              stmtBuilder ++= stmts
              refBuilder += lir.Reference(name.name, tpe)

              nextIdx
          }

          val stmts = stmtBuilder.result()
          val refs = refBuilder.result()

          val trueRef = lir.Literal(1, BackendType.boolTpe)
          val results = (patterns zip refs)
            .map{ case (pattern, ref) => pattern -> DataInstance(pattern.tpe, ref) }
            .map{ case (pattern, inst) => runPattern(inst, pattern) }

          val conds = results.map(_.instance.asInstanceOf[DataInstance])
          val patternStmts = results.flatMap(_.stmts)

          val leftNodes = Vector.newBuilder[lir.Node]
          val condition = conds.filter(_.refer == trueRef).foldLeft[lir.Expr](variantEq) {
            case (left, right) =>
              val (leftNode, leftRef) = makeNode(left)
              leftNodes += leftNode

              lir.Ops(
                PrimOps.And,
                Vector(leftRef, right.refer),
                Vector.empty,
                left.tpe
            )
          }

          val condName = stack.next("_GEN")
          val condRef = lir.Reference(condName.name, condition.tpe)
          val connect = lir.Node(condName.name, condition, condition.tpe)
          val returnStmts = litNode +: (stmts ++ leftNodes.result() ++ patternStmts) :+ connect
          val boolTpe = toBackendType(Type.boolTpe)
          val returnInst = DataInstance(boolTpe, condRef)

          RunResult(returnStmts, returnInst)
      }
    }

    def runCase(instance: DataInstance, caseExpr: backend.Case, retLoc: Option[lir.Reference]): (Vector[lir.Stmt], lir.When) = {
      val RunResult(patternStmts, condInstance: DataInstance) = runPattern(instance, caseExpr.pattern)
      val bodyStmts = caseExpr.stmts.flatMap(runStmt)
      val RunResult(exprStmts, retInstance: DataInstance) = runExpr(caseExpr.ret)

      val retConnect = retLoc.map(loc => lir.Assign(loc, retInstance.refer))
      val conseqStmts = bodyStmts ++ exprStmts ++ retConnect
      val when = lir.When(condInstance.refer, conseqStmts, Vector.empty)

      (patternStmts, when)
    }

    val backend.Match(matched, cases, tpe) = matchExpr
    val instance = stack.lookup(stack.refer(matched.id))

    val retWireOpt =
      if(tpe.symbol == Symbol.unit) None
      else {
        val retName = stack.next("_GEN")
        lir.Wire(retName.name, tpe).some
      }

    val retRefOpt = retWireOpt.map(wire => lir.Reference(wire.name, wire.tpe))
    val RunResult(resStmts, retInstance) = retRefOpt.map(ref => RunResult(Vector.empty, DataInstance(tpe, ref))).getOrElse(DataInstance.unit())
    val retInvalid = retRefOpt.map(ref => lir.Invalid(ref.name))
    val retStmts = Vector(retWireOpt, retInvalid).flatten

    retRefOpt.foreach(ref => stack.append(Name(ref.name), retInstance))

    val (patternStmtss, conds) = cases.map(runCase(instance.asInstanceOf[DataInstance], _, retRefOpt)).unzip

    val patternStmts = patternStmtss.flatten
    val caseConds = conds.foldRight[lir.Stmt](lir.Stop()) {
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
    def buildIndirectAccessCond(interface: MethodContainer, fromName: String)(targetBuilder: String => lir.Ref): (Option[lir.Invalid], Vector[lir.Stmt]) = {
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
          lir.Assign(dst, targetBuilder(interface.retName)).some
        }
      val retInvalid = assignOpt.map(_ => lir.Invalid(interface.retName))

      val params = interface.params.map { case (name, _) => targetBuilder(name) }.toVector
      val args = interface.params.map { case (name, tpe) => fromRef(name, tpe) }.toVector
      val connects = (params zip args).map { case (param, arg) => lir.Assign(param, arg) }
      val (activeLitNode, activeLitRef) = makeNode(lir.Literal(1, BackendType.boolTpe))
      val activate = lir.Assign(targetBuilder(interface.activeName), activeLitRef)
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

        val targetName: String => lir.Ref = refer match {
          case ModuleLocation.This => (name: String) => lir.Reference(name, tpe)
          case ModuleLocation.Upper(target) => name: String => lir.Reference(target + "_" + name, tpe)
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

        val target: String => lir.Ref = refer match {
          case ModuleLocation.This => throw new ImplementationErrorException("refer this module as sibling module")
          case ModuleLocation.Sub(refer) => (name: String) => lir.SubField(refer, name, tpe)
          case ModuleLocation.Upper(refer) => (name: String) => lir.Reference(refer + "$" + name, tpe)
        }

        val (invalid, stmtss) = siblings.map(buildIndirectAccessCond(_, fromName)(target)).unzip

        (stmts ++ invalid.flatten, stmtss.flatten)
    }.unzip

    // Assign default values to submodule's input or sibling interfaces
    // default:
    //   active     = false
    //   parameters = undefined
    val inputInitss = ctx.interfaces(construct.tpe) // get interfaces submodule has
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
          val paramInvalid = params.map(p => lir.Invalid(p.name))

          Vector(activeOffNode, activeOff) ++ paramInvalid
      }

    val parentStmts = parentStmtss.toVector.flatten
    val siblingStmts = siblingStmtss.toVector.flatten
    val inputStmts = inputInitss.flatten
    val conds = (siblingCondss.toVector ++ parentCondss.toVector).flatten

    val stmts = inputStmts ++ parentStmts ++ siblingStmts ++ conds

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
      /*
      tpe match {
        case ir.UIntType(_) => Vector(refer)
        case ir.BundleType(fields) =>
          val refers = fields.flatMap {
            field =>
              val underRefer = ir.SubField(refer, field.name, field.tpe)
              makeLeafs(field.tpe, underRefer)
          }

          refers.toVector
        case ir.VectorType(tpe, length) =>
          (0 to length).flatMap(idx => makeLeafs(tpe, ir.SubIndex(refer, idx, tpe))).toVector
      }
      */

      tpe.symbol match {
        case sym if sym == Symbol.bit => Vector(refer)
        case sym if sym == Symbol.vec =>
          val HPElem.Num(length) = tpe.hargs.head
          val elemTpe = tpe.targs.head
          (0 to length).flatMap(idx => makeLeafs(elemTpe, lir.SubIndex(refer, idx, elemTpe))).toVector
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
    val value = insts
      .map(_.asInstanceOf[DataInstance])
      .flatMap(inst => makeLeafs(inst.tpe, inst.refer))
      .reduceLeftOption[lir.Ref] {
        case (prefix, refer) =>
          val HPElem.Num(prefixWidth) = prefix.tpe.hargs.head
          val HPElem.Num(referWidth) = refer.tpe.hargs.head
          val catWidth = prefixWidth + referWidth
          val cat = lir.Ops(PrimOps.Cat, Vector(refer, prefix), Vector.empty, BackendType.bitTpe(catWidth))
          val (tempNode, tempRef) = makeNode(cat)

          temporaryNodes += tempNode
          tempRef
      }
      .getOrElse(lir.Literal(0, BackendType.unitTpe))
    val (valueNode, valueRef) = makeNode(value)

    val variants = enum.tpe.symbol.tpe.declares
      .toMap.toVector
      .sortWith { case ((left, _), (right, _)) => left < right }
      .map { case (_, symbol) => symbol }
    val variantWidth = atLeastLength(variants.length).toInt
    val flagValue = variants.zipWithIndex
      .find { case (symbol, _) => symbol == enum.variant }
      .map { case (_, idx) => lir.Literal(idx, BackendType.bitTpe(variantWidth)) }
      .getOrElse(throw new ImplementationErrorException(s"${enum.variant} was not found"))
    val (flagNode, flagRef) = makeNode(flagValue)

    val enumName = stack.next("_ENUM")
    val enumRef = lir.Reference(enumName.name, enum.tpe)
    val wireDef = lir.Wire(enumName.name, enum.tpe)

    val connectFlag = lir.Assign(
      lir.SubField(enumRef, "_member", flagValue.tpe),
      flagRef
    )
    val connectData = lir.Assign(
      lir.SubField(enumRef, "_data", value.tpe),
      valueRef
    )

    val runResultStmts = wireDef +: (temporaryNodes.result() ++ Vector(valueNode, flagNode, connectFlag, connectData))
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

    val stmts = assignRegParams(stateContainer.params, goto.state.args)
    val RunResult(unitStmts, unitInstance) = DataInstance.unit()

    RunResult(Vector(literalNode, changeState) ++ stmts ++ unitStmts, unitInstance)
  }

  def runGenerate(generate: backend.Generate)(implicit stack: StackFrame, ctx: FirrtlContext, global: GlobalData): RunResult = {
    val stageContainer = ctx.stages(stack.lookupThis.get.tpe).find(_.label == generate.stage).get
    val activeRef = lir.Reference(generate.stage.activeName, BackendType.boolTpe)
    val (literalNode, literalRef) = makeNode(lir.Literal(1, BackendType.boolTpe))
    val activate = lir.Assign(activeRef, literalRef)

    val (state, node) = generate.state match {
      case None => (None, None)
      case Some(backend.State(label, _)) =>
        val stateWidth = atLeastLength(stageContainer.states.length).toInt
        val stateTpe = BackendType.bitTpe(stateWidth)
        val stateRef = lir.Reference(stageContainer.label.stateName, stateTpe)
        val (stateValNode, stateValRef) = makeNode(lir.Literal(label.index, stateTpe))

        (lir.Assign(stateRef, stateValRef).some, stateValNode.some)
    }

    val stageAssigns = assignRegParams(stageContainer.params, generate.args)
    val stateAssigns = generate.state.map {
      state =>
        val backend.State(stateLabel, args) = state
        val stateContainer = stageContainer.states.find(_.label.index == stateLabel.index).get

        assignRegParams(stateContainer.params, args)
    }.getOrElse(Vector.empty)

    val stmts = Vector(literalNode, activate) ++ (node.toVector ++ state.toVector ++ stageAssigns ++ stateAssigns)
    val RunResult(unitStmts, unit) = DataInstance.unit()

    RunResult(stmts ++ unitStmts, unit)
  }

  private def assignRegParams(params: ListMap[String, BackendType], args: Vector[backend.Term.Temp])(implicit stack: StackFrame, ctx: FirrtlContext, global: GlobalData): Vector[lir.Stmt] = {
    val instances = args.map{ case backend.Term.Temp(id, _) => stack.refer(id) }.map(stack.lookup).map(_.asInstanceOf[DataInstance])
    val paramRefs = params.map{ case (name, tpe) => lir.Reference(name, tpe) }

    (paramRefs zip instances).map{ case (p, a) => lir.Assign(p, a.refer)}.toVector
  }

  def runReturn(ret: backend.Return)(implicit stack: StackFrame, ctx: FirrtlContext, global: GlobalData): RunResult = {
    val RunResult(stmts, instance) = runExpr(ret.expr)
    val DataInstance(_, refer) = instance
    val retRef = lir.Reference(ret.proc.retName, ret.tpe)
    val assign = lir.Assign(retRef, refer)
    val RunResult(unitStmts, unit) = DataInstance.unit()

    RunResult((stmts :+ assign) ++ unitStmts, unit)
  }

  def runCommence(commence: backend.Commence)(implicit stack: StackFrame, ctx: FirrtlContext, global: GlobalData): RunResult = {
    val stmts = activateProcBlock(commence.procLabel, commence.blkLabel, commence.args)
    val pointer = lir.Pointer(commence.procLabel.symbol.path, commence.tpe)
    val (pointerNode, pointerRef) = makeNode(pointer)
    val inst = DataInstance(commence.tpe, pointerRef)

    RunResult(stmts :+ pointerNode, inst)
  }

  def runRelayBlock(relay: backend.RelayBlock)(implicit stack: StackFrame, ctx: FirrtlContext, global: GlobalData): RunResult = {
    val RunResult(unitStmts, unit) = DataInstance.unit()

    RunResult(
      activateProcBlock(relay.procLabel, relay.blkLabel, relay.args) ++ unitStmts,
      unit
    )
  }

  def activateProcBlock(procLabel: ProcLabel, blkLabel: ProcBlockLabel, args: Vector[backend.Term.Temp])(implicit stack: StackFrame, ctx: FirrtlContext, global: GlobalData): Vector[lir.Stmt] = {
    val procContainer = ctx.procs(stack.lookupThis.get.tpe).find(_.label == procLabel).get

    val activeRef = lir.Reference(blkLabel.activeName, BackendType.boolTpe)
    val (litNode, litRef) = makeNode(lir.Literal(1, BackendType.boolTpe))
    val activate = lir.Assign(activeRef, litRef)

    val blkContainer = procContainer.blks.find(_.label == blkLabel).get
    val assigns = (blkContainer.params.toVector zip args).map {
      case ((param, tpe), arg) =>
        val paramRef = lir.Reference(param, tpe)
        val argRef = lir.Reference(stack.refer(arg.id).name, tpe)
        lir.Assign(paramRef, argRef)
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
}
