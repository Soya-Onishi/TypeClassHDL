package tchdl.backend

import tchdl.backend.{ast => backend}
import tchdl.util._
import tchdl.util.TchdlException._
import firrtl.{PrimOps, ir}

import scala.annotation.tailrec
import scala.collection.immutable.ListMap
import scala.collection.mutable

object FirrtlCodeGen {
  val clockName = "CLK"
  val resetName = "RESET"
  val clockRef = ir.Reference(clockName, ir.ClockType)
  val resetRef = ir.Reference(resetName, ir.UIntType(ir.IntWidth(1)))

  case class ElaboratedModule(
    ports: Vector[ir.Port],
    instances: Vector[ir.DefInstance],
    components: Vector[ir.Statement with ir.IsDeclaration],
    inits: Vector[ir.Statement],
    bodies: Vector[ir.Statement],
    future: Future,
  )
  object ElaboratedModule {
    def empty: ElaboratedModule =
      ElaboratedModule(Vector.empty, Vector.empty, Vector.empty, Vector.empty, Vector.empty, Future.empty)
  }

  case class BuildResult[T](stmts: Vector[ir.Statement], future: Future, component: T)

  case class FirrtlContext(
    interfaces: Map[BackendType, Vector[MethodContainer]],
    stages: Map[BackendType, Vector[StageContainer]],
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

  def exec(topModule: BackendType, modules: Vector[ModuleContainer], methods: Vector[MethodContainer])(implicit global: GlobalData): ir.Circuit = {
    val interfaceTable = modules.map(module => module.tpe -> module.bodies.flatMap(_.interfaces)).toMap
    val stageTable = modules.map(module => module.tpe -> module.bodies.flatMap(_.stages)).toMap
    val methodTable = methods
      .collect { case method if method.label.accessor.isDefined => method }
      .groupBy(_.label.accessor.get)
    val functionTable = methods.collect { case method if method.label.accessor.isEmpty => method }

    val firrtlModules = modules.map(buildModule(_, interfaceTable, stageTable, methodTable, functionTable))

    val circuitName = topModule.toFirrtlString
    ir.Circuit(ir.NoInfo, firrtlModules, circuitName)
  }

  def buildModule(
    module: ModuleContainer,
    interfaces: Map[BackendType, Vector[MethodContainer]],
    stages: Map[BackendType, Vector[StageContainer]],
    methods: Map[BackendType, Vector[MethodContainer]],
    functions: Vector[MethodContainer]
  )(implicit global: GlobalData): ir.Module = {
    val instance = ModuleInstance(module.tpe, ModuleLocation.This)
    val ctx = FirrtlContext(interfaces, stages, methods, functions)
    val stack = StackFrame(instance)

    val elaborateds = module.bodies map { moduleBody =>
      moduleBody.hps
        .map { case (name, elem) => stack.next(name) -> elem }
        .foreach {
          case (name, HPElem.Num(num)) => stack.append(name, DataInstance(num))
          case (name, HPElem.Str(str)) => stack.append(name, StringInstance(str))
        }

      // fields into stack
      moduleBody.fields.foreach { field =>
        val name = field.toFirrtlString
        stack.lock(name)
        val ref = ir.Reference(stack.refer(name).name, ir.UnknownType)
        val instance =
          if(field.flag.hasFlag(Modifier.Child)) ModuleInstance(field.tpe, ModuleLocation.Sub(ref))
          else DataInstance(field.tpe, ref)

        stack.append(stack.refer(name), instance)
      }

      val inputs = moduleBody.fields
        .filter(_.flag.hasFlag(Modifier.Input))
        .map(runInput(_)(stack, ctx, global))

      val outputs = moduleBody.fields
        .filter(_.flag.hasFlag(Modifier.Output))
        .map(runOutput(_)(stack, ctx, global))

      val internals = moduleBody.fields
        .filter(_.flag.hasFlag(Modifier.Internal))
        .map(runInternal(_)(stack, ctx, global))

      val registers = moduleBody.fields
        .filter(_.flag.hasFlag(Modifier.Register))
        .map(runRegister(_)(stack, ctx, global))

      val modules = moduleBody.fields
        .filter(_.flag.hasFlag(Modifier.Child))
        .filter(_.tpe.symbol != Symbol.mem)
        .map(runSubModule(_)(stack, ctx, global))

      val memories = moduleBody.fields
        .filter(_.flag.hasFlag(Modifier.Child))
        .filter(_.tpe.symbol == Symbol.mem)
        .map(runMemory(_)(stack, ctx, global))

      val alwayss = moduleBody.always.map(runAlways(_)(stack, ctx, global))
      val (inputInterContainers, normalInterContainers) = moduleBody.interfaces.partition{ interface =>
        val symbol = interface.label.symbol
        symbol.hasFlag(Modifier.Input) || symbol.hasFlag(Modifier.Sibling)
      }
      val inputInterfaces = inputInterContainers.map(buildInputInterfaceSignature(_)(stack, global))
      val normalInterfaces = normalInterContainers.map(buildInternalInterfaceSignature(_)(stack, global))
      val interfaceBodies = moduleBody.interfaces.map(runInterface(_)(stack, ctx, global))
      val stageSigs = moduleBody.stages.map(buildStageSignature(_)(stack, ctx, global))
      val stageBodies = moduleBody.stages.map(runStage(_)(stack, ctx, global))

      val clk = ir.Port(ir.NoInfo, clockName, ir.Input, ir.ClockType)
      val reset = ir.Port(ir.NoInfo, resetName, ir.Input, ir.UIntType(ir.IntWidth(1)))
      val ports = Vector(clk, reset) ++ inputs.flatMap(_.component) ++ outputs.flatMap(_.component) ++ inputInterfaces.flatMap(_.component)
      val (instances, accessCondss) = modules.map(_.component).unzip
      val components = internals.flatMap(_.component) ++ registers.flatMap(_.component) ++ normalInterfaces.flatMap(_.component) ++ stageSigs.flatMap(_.component)

      val interfaceInits = inputs.flatMap(_.stmts) ++ outputs.flatMap(_.stmts) ++ internals.flatMap(_.stmts)
      val componentInits = registers.flatMap(_.stmts) ++ modules.flatMap(_.stmts) ++ memories.flatMap(_.stmts) ++ inputInterfaces.flatMap(_.stmts) ++ normalInterfaces.flatMap(_.stmts) ++ stageSigs.flatMap(_.stmts)
      val inits = interfaceInits ++ componentInits

      val bodies = accessCondss.flatten ++ interfaceBodies.flatMap(_.stmts) ++ stageBodies.flatMap(_.stmts) ++ alwayss.flatMap(_.stmts)

      val interfaceFutures = inputs.map(_.future) ++ outputs.map(_.future) ++ internals.map(_.future)
      val componentFutures = registers.map(_.future) ++ modules.map(_.future) ++ memories.map(_.future)
      val bodyFutures =
        alwayss.map(_.future) ++ inputInterfaces.map(_.future) ++ normalInterfaces.map(_.future) ++
        registers.map(_.future) ++ modules.map(_.future) ++ memories.map(_.future) ++
        stageSigs.map(_.future) ++ interfaceBodies.map(_.future) ++ stageBodies.map(_.future)

      val futures = interfaceFutures ++ componentFutures ++ bodyFutures
      val future = futures.foldLeft(Future.empty)(_ + _)

      ElaboratedModule(ports, instances, components, inits, bodies, future)
    }

    val moduleField = global.lookupFields(module.tpe)
    val (upperFutures, upperPorts, upperPortInits) = moduleField
      .map { case (name, tpe) => buildUpperModule(name, tpe)(ctx, global) }
      .toVector
      .unzip3

    val elaborated = elaborateds.foldLeft(ElaboratedModule.empty) {
      case (acc, module) =>
        val ports = acc.ports ++ module.ports
        val future = acc.future + module.future
        val instances = acc.instances ++ module.instances
        val inits = acc.inits ++ module.inits
        val bodies = acc.bodies ++ module.bodies
        val components = acc.components ++ module.components

        ElaboratedModule(ports, instances, components, inits, bodies, future)
    }

    val futureStmts = buildFuture(upperFutures.foldLeft(elaborated.future)(_ + _))
    val ports = elaborated.ports ++ upperPorts.flatten
    val inits = upperPortInits.flatten ++ elaborated.inits

    val moduleName = module.tpe.toFirrtlString
    val block = ir.Block(elaborated.instances ++ elaborated.components ++ inits ++ futureStmts ++ elaborated.bodies)

    ir.Module(ir.NoInfo, moduleName, ports, block)
  }

  def runInput(field: FieldContainer)(implicit stack: StackFrame, ctx: FirrtlContext, global: GlobalData): BuildResult[Vector[ir.Port]] = {
    val (stmtss, futures) = field.code.map(runStmt).unzip
    val retExpr = field.ret.map(throw new ImplementationErrorException("input wire with init expression is not supported yet"))
    val (normalPortOpt, futurePorts) = port(field.toFirrtlString, field.tpe, ir.Input)
    val ports = (normalPortOpt ++ futurePorts).toVector
    val future = futures.foldLeft(Future.empty)(_ + _)

    BuildResult(stmtss.flatten, future, ports)
  }

  def runOutput(field: FieldContainer)(implicit stack: StackFrame, ctx: FirrtlContext, global: GlobalData): BuildResult[Vector[ir.Port]] = {
    val (stmtss, futures) = field.code.map(runStmt).unzip
    val fieldRef = ir.Reference(field.toFirrtlString, ir.UnknownType)
    val (retFuture, retStmt) = field.ret.map(runExpr) match {
      case None => (Future.empty, Vector.empty)
      case Some(RunResult(future, stmts, inst: DataInstance)) =>
        val (connectFuture, connectOpt) = connect(fieldRef, inst)
        (future + connectFuture, stmts ++ connectOpt)
    }

    val future = futures.foldLeft(retFuture)(_ + _)
    val (normalPortOpt, futurePorts) = port(field.toFirrtlString, field.tpe, ir.Output)
    val ports = (normalPortOpt ++ futurePorts).toVector

    BuildResult(stmtss.flatten ++ retStmt, future, ports)
  }

  def runInternal(field: FieldContainer)(implicit stack: StackFrame, ctx: FirrtlContext, global: GlobalData): BuildResult[Vector[ir.DefWire]] = {
    val (stmtss, stmtFutures) = field.code.map(runStmt).unzip
    val (retFuture, retStmt) = field.ret.map(runExpr) match {
      case None => (Future.empty, Vector.empty)
      case Some(RunResult(future, stmts, inst: DataInstance)) =>
        val fieldRef = ir.Reference(field.toFirrtlString, ir.UnknownType)
        val (connectFuture, connectOpt) = connect(fieldRef, inst)
        (future + connectFuture, stmts ++ connectOpt)
    }

    val future = stmtFutures.foldLeft(retFuture)(_ + _)
    val (normalWireOpt, futureWires) = wire(field.toFirrtlString, field.tpe)
    val wires = (normalWireOpt ++ futureWires).toVector

    BuildResult(stmtss.flatten ++ retStmt, future, wires)
  }

  def runRegister(field: FieldContainer)(implicit stack: StackFrame, ctx: FirrtlContext, global: GlobalData): BuildResult[Vector[ir.Statement with ir.IsDeclaration]] = {
    val (stmtss, futures) = field.code.map(runStmt).unzip
    val (regOpt, wires) = register(field.toFirrtlString, field.tpe)
    val (retFuture, retStmts, regInitOpt) = field.ret.map(runExpr) match {
      case None => (Future.empty, Vector.empty, Option.empty)
      case Some(RunResult(retFuture, stmts, inst: DataInstance)) =>
        val fieldRef = ir.Reference(field.toFirrtlString, ir.UnknownType)
        val (future, connectOpt) = connect(fieldRef, inst)
        (future + retFuture, stmts, connectOpt.map(_.expr))
    }

    val actualRegOpt = (regOpt zip regInitOpt)
      .map{ case (reg, init) => reg.copy(init = init) }
      .headOption
      .orElse(regOpt)

    val decls = (actualRegOpt ++ wires).toVector
    val future = futures.foldLeft(retFuture)(_ + _)

    BuildResult(stmtss.flatten ++ retStmts, future, decls)
  }

  def runSubModule(field: FieldContainer)(implicit stack: StackFrame, ctx: FirrtlContext, global: GlobalData): BuildResult[(ir.DefInstance, Vector[ir.Conditionally])] = {
    val (stmtss, _) = field.code.map(runStmt).unzip
    val (future, retStmts) = field.ret
      .map(runExpr)
      .map { case RunResult(future, stmts, _) => (future, stmts) }
      .getOrElse(throw new ImplementationErrorException("sub module instance expression must be there"))

    val tpeString = field.tpe.toFirrtlString
    val module = ir.DefInstance(ir.NoInfo, field.toFirrtlString, tpeString)

    val subModuleStmts = stmtss.flatten ++ retStmts
    val (conds, inits) = subModuleStmts.collectPartition { case cond: ir.Conditionally => cond }

    BuildResult(inits, future, (module, conds))
  }

  def runAlways(always: AlwaysContainer)(implicit stack: StackFrame, ctx: FirrtlContext, global: GlobalData): BuildResult[Unit] = {
    val (stmtss, futures) = always.code.map(runStmt).unzip
    val stmts = stmtss.flatten
    val future = futures.foldLeft(Future.empty)(_ + _)

    BuildResult(stmts, future, ())
  }

  def runMemory(memory: FieldContainer)(implicit stack: StackFrame, ctx: FirrtlContext, global: GlobalData): BuildResult[Unit] = {
    val dataType = toFirrtlType(memory.tpe.targs.head)
    val HPElem.Num(depth) = memory.tpe.hargs(0)
    val HPElem.Num(readPort) = memory.tpe.hargs(2)
    val HPElem.Num(writePort) = memory.tpe.hargs(3)
    val HPElem.Num(readLatency) = memory.tpe.hargs(4)
    val HPElem.Num(writeLatency) = memory.tpe.hargs(5)

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

    BuildResult(memDef +: (readStmts ++ writeStmts), Future.empty, ())
  }

  def buildStageSignature(stage: StageContainer)(implicit stack: StackFrame, ctx: FirrtlContext, global: GlobalData): BuildResult[Vector[ir.Statement with ir.IsDeclaration]] = {
    def buildParams(paramPairs: Vector[(String, BackendType)]): (Future, Vector[ir.DefRegister], Vector[ir.DefWire]) = {
      paramPairs.foreach { case (name, _) => stack.lock(name) }

      val params = paramPairs
        .map { case (name, tpe) => stack.refer(name) -> tpe }
        .map { case (name, tpe) => name -> StructInstance(tpe, ir.Reference(name.name, ir.UnknownType)) }

      params.foreach { case (name, instance) => stack.append(name, instance) }

      val (normalDefss, futureDefss) = params.map{ case (name, inst) => register(name.name, inst.tpe) }.unzip
      val regs = normalDefss.flatten
      val wires = futureDefss.flatten
      val future = wires.foldLeft(Future.empty) {
        case (acc, wire) =>
          val future = Future(Map.empty, Map(ir.Reference(wire.name, ir.UnknownType) -> UsageStyle.Field))
          acc + future
      }

      (future, regs, wires)
    }

    val (stageFuture, stageRegs, stageWires) = buildParams(stage.params.toVector)
    val (stateFuture, stateRegs, stateWires) = buildParams(stage.states.flatMap(_.params))

    val active = ir.DefRegister(
      ir.NoInfo,
      stage.activeName,
      ir.UIntType(ir.IntWidth(1)),
      clockRef,
      resetRef,
      ir.UIntLiteral(0)
    )

    def log2(x: Double): Double = math.log10(x) / math.log10(2.0)

    def stateWidth(x: Double): Double = {
      val width = (math.ceil _ compose log2) (x)

      if (width == 0) 1
      else width
    }

    val state =
      if (stage.states.isEmpty) None
      else Some(ir.DefRegister(
        ir.NoInfo,
        stage.stateName,
        ir.UIntType(ir.IntWidth(stateWidth(stage.states.length).toInt)),
        clockRef,
        resetRef,
        ir.UIntLiteral(0)
      ))

    val ret =
      if (stage.ret == toBackendType(Type.unitTpe)) None
      else Some(ir.DefWire(ir.NoInfo, stage.retName, toFirrtlType(stage.ret)))

    val retRef = ir.Reference(stage.retName, ir.UnknownType)
    val futureRet =
      if (stage.ret == toBackendType(Type.unitTpe)) Future.empty
      else Future(Map.empty, Map(retRef -> UsageStyle.Field))

    val wires = stageWires ++ stateWires ++ ret
    val regs = active +: (stageRegs ++ stateRegs ++ state)
    val future = stageFuture + stateFuture + futureRet

    BuildResult(Vector.empty, future, wires ++ regs)
  }

  def runStage(stage: StageContainer)(implicit stack: StackFrame, ctx: FirrtlContext, global: GlobalData): BuildResult[Unit] = {
    val (stmtss, futures) = stage.code.map(runStmt).unzip
    val (states, stateFutures) = stage.states.zipWithIndex.map {
      case (state, idx) =>
        val (stateStmtss, stateFutures) = state.code.map(runStmt).unzip
        val stateRef = ir.Reference(stage.stateName, ir.UnknownType)
        val cond = ir.Conditionally(
          ir.NoInfo,
          ir.DoPrim(PrimOps.Eq, Seq(stateRef, ir.UIntLiteral(idx)), Seq.empty, ir.UnknownType),
          ir.Block(stateStmtss.flatten),
          ir.EmptyStmt
        )

        (cond, stateFutures.foldLeft(Future.empty)(_ + _))
    }.unzip

    val cond = ir.Conditionally(
      ir.NoInfo,
      ir.Reference(stage.activeName, ir.UnknownType),
      ir.Block(stmtss.flatten ++ states),
      ir.EmptyStmt
    )

    val future = (futures ++ stateFutures).foldLeft(Future.empty)(_ + _)

    BuildResult(Vector(cond), future, ())
  }

  private def buildInputInterfaceSignature(interface: MethodContainer)(implicit stack: StackFrame, global: GlobalData): BuildResult[Vector[ir.Port]] = {
    interface.params.foreach { case (name, _) => stack.lock(name) }
    val retTpe = interface.label.symbol.tpe.asMethodType.returnType
    val isUnitRet = retTpe.origin == Symbol.unit

    val params = interface.params
      .map { case (name, tpe) => stack.refer(name) -> tpe }
      .map { case (name, tpe) => name -> DataInstance(tpe, ir.Reference(name.name, ir.UnknownType)) }
      .toVector

    params.foreach { case (name, instance) => stack.append(name, instance) }

    val active = ir.Port(ir.NoInfo, interface.activeName, ir.Input, ir.UIntType(ir.IntWidth(1)))
    val (normalParams, futureParams) = params.map { case (name, inst) => port(name.name, inst.tpe, ir.Input) }.unzip
    val paramPorts = normalParams.flatten ++ futureParams.flatten
    val retName =
      if(isUnitRet) None
      else Some(interface.retName)

    val (normalOutputIter, futureOutputIter) = retName.map(name => port(name, interface.retTpe, ir.Output)).unzip
    val normalOutputOpt = normalOutputIter.headOption.flatten
    val futureOutputs = futureOutputIter.flatten
    val retPorts = (normalOutputOpt ++ futureOutputs).toVector

    val retRef = retName.map(ir.Reference(_, ir.UnknownType))
    val retFuture = futureOutputs.foldLeft(Future.empty){
      case (acc, output) =>
        val ref = ir.Reference(output.name, ir.UnknownType)
        acc + Future(Map.empty, Map(ref -> UsageStyle.Field))
    }

    val retInvalid = retRef.map(ir.IsInvalid(ir.NoInfo, _))
    val ports = active +: (paramPorts ++ retPorts)

    BuildResult(retInvalid.toVector, retFuture, ports)
  }

  private def buildInternalInterfaceSignature(interface: MethodContainer)(implicit stack: StackFrame, global: GlobalData): BuildResult[Vector[ir.DefWire]] = {
    interface.params.foreach { case (name, _) => stack.lock(name) }
    val retTpe = interface.label.symbol.tpe.asMethodType.returnType
    val isUnitRet = retTpe.origin == Symbol.unit
    val isFutureRet = retTpe.origin == Symbol.future

    val params = interface.params
      .map { case (name, tpe) => stack.refer(name) -> tpe }
      .map { case (name, tpe) => name -> DataInstance(tpe, ir.Reference(name.name, ir.UnknownType)) }
      .toVector
    params.foreach { case (name, instance) => stack.append(name, instance) }

    val active = ir.DefWire(ir.NoInfo, interface.activeName, ir.UIntType(ir.IntWidth(1)))
    val activeOff = ir.Connect(ir.NoInfo, ir.Reference(interface.activeName, ir.UnknownType), ir.UIntLiteral(0))
    val paramDefs = interface.params.map{ case (name, tpe) => ir.DefWire(ir.NoInfo, name, toFirrtlType(tpe)) }.toVector
    val paramInvalids = params
      .filter { case (_, DataInstance(tpe, _)) => tpe.symbol != Symbol.future }
      .map { case (name, _) => ir.IsInvalid(ir.NoInfo, ir.Reference(name.name, ir.UnknownType)) }

    val retName =
      if(isUnitRet) None
      else Some(interface.retName)

    val retWire = retName.map(ir.DefWire(ir.NoInfo, _, toFirrtlType(interface.retTpe)))
    val retRef = retName.map(ir.Reference(_, ir.UnknownType))
    val retInit = retRef.map(ir.IsInvalid(ir.NoInfo, _))
    val retFuture =
      if (isFutureRet) Future(Map.empty, Map(retRef.get -> UsageStyle.Field))
      else Future.empty

    val future = params
      .map { case (name, DataInstance(tpe, _)) => name -> tpe }
      .filter { case (_, tpe) => tpe.symbol == Symbol.future }
      .map { case (name, tpe) => ir.Reference(name.name, ir.UnknownType) -> tpe }
      .map { case (refer, _) => Future(Map.empty, Map(refer -> UsageStyle.Field)) }
      .foldLeft(retFuture)(_ + _)

    val wires = active +: (paramDefs ++ retWire)
    val inits = activeOff +: (paramInvalids ++ retInit)

    BuildResult(inits, future, wires)
  }

  def runInterface(interface: MethodContainer)(implicit stack: StackFrame, ctx: FirrtlContext, global: GlobalData): BuildResult[Unit] = {
    val (stmts, stmtFutures) = interface.code.map(runStmt(_)).unzip
    val RunResult(runFuture, retStmts, instance: DataInstance) = runExpr(interface.ret)
    val methodRetTpe = interface.label.symbol.tpe.asMethodType.returnType
    val (retFuture, retConnect) =
      if (methodRetTpe == Type.unitTpe) (Future.empty, Option.empty)
      else connect(ir.Reference(interface.retName, ir.UnknownType), instance)

    val future = stmtFutures.foldLeft(runFuture + retFuture)(_ + _)
    val cond = ir.Conditionally(
      ir.NoInfo,
      ir.Reference(interface.activeName, ir.UnknownType),
      ir.Block(stmts.flatten ++ retStmts ++ retConnect),
      ir.EmptyStmt
    )

    BuildResult(Vector(cond), future, ())
  }

  def buildFuture(future: Future): Vector[ir.Statement] = {
    def memberRef(expr: ir.Expression): ir.SubField = ir.SubField(expr, "_member", ir.UnknownType)
    def dataRef(expr: ir.Expression): ir.SubField = ir.SubField(expr, "_data", ir.UnknownType)

    def buildConnect(name: ir.Expression, froms: Vector[ir.Expression]): Vector[ir.Connect] = {
      val locMember = memberRef(name)
      val locData = dataRef(name)
      val fromMembers = froms.map(from => ir.SubField(from, "_member", ir.UnknownType))
      val fromDatas = froms.map(from => ir.SubField(from, "_data", ir.UnknownType))

      val memberOr = fromMembers.foldLeft[ir.Expression](ir.UIntLiteral(0)) {
        case (left, right) => ir.DoPrim(PrimOps.Or, Seq(left, right), Seq.empty, ir.UnknownType)
      }

      val dataOr = fromDatas.foldLeft[ir.Expression](ir.UIntLiteral(0)) {
        case (left, right) => ir.DoPrim(PrimOps.Or, Seq(left, right), Seq.empty, ir.UnknownType)
      }

      val memberConnect = ir.Connect(ir.NoInfo, locMember, memberOr)
      val dataConnect = ir.Connect(ir.NoInfo, locData, dataOr)

      Vector(memberConnect, dataConnect)
    }

    def buildConstructor(expr: ir.Expression): Vector[ir.Connect] = {
      val connectMember = ir.Connect(ir.NoInfo, memberRef(expr), ir.UIntLiteral(0))
      val connectData = ir.Connect(ir.NoInfo, dataRef(expr), ir.UIntLiteral(0))

      Vector(connectMember, connectData)
    }

    val (wiresOpts, connectss) = future.futures.toVector.map {
      case (refer @ ir.Reference(name, _), UsageStyle.Local(tpe)) =>
        val froms = future.froms.getOrElse(refer, Vector.empty)
        val wire = ir.DefWire(ir.NoInfo, name, tpe)
        (Some(wire), buildConnect(refer, froms))
      case (refer @ ir.Reference(name, _), UsageStyle.Constructor(tpe)) =>
        val wire = ir.DefWire(ir.NoInfo, name, tpe)
        (Some(wire), buildConstructor(refer))
      case (refer, _) =>
        val froms = future.froms.getOrElse(refer, Vector.empty)
        (None, buildConnect(refer, froms))
    }.unzip

    val wires = wiresOpts.flatten
    val connects = connectss.flatten

    wires ++ connects
  }

  def buildUpperModule(moduleName: String, tpe: BackendType)(implicit ctx: FirrtlContext, global: GlobalData): (Future, Vector[ir.Port], Vector[ir.Statement]) = {
    val allInterfaces = ctx.interfaces.getOrElse(tpe, Vector.empty)

    val interfaces = allInterfaces.filter {
      interface =>
        val isSibling = interface.label.symbol.hasFlag(Modifier.Sibling)
        val isParent = interface.label.symbol.hasFlag(Modifier.Parent)

        isSibling || isParent
    }

    val pairs = interfaces.map {
      interface =>
        def buildName(name: String): String = moduleName + "$" + name

        val activeName = buildName(interface.activeName)
        val retName = buildName(interface.retName)

        val activePort = ir.Port(ir.NoInfo, activeName, ir.Output, ir.UIntType(ir.IntWidth(1)))
        val (normalRetPortOpt, futureRetPorts) =
          if (interface.ret.tpe == toBackendType(Type.unitTpe)) (Option.empty, Vector.empty)
          else port(retName, interface.ret.tpe, ir.Input)
        val retPorts = (normalRetPortOpt ++ futureRetPorts).toVector

        val (paramNormalPortss, paramFuturePortss) = interface.params
          .map { case (name, tpe) => port(buildName(name), tpe, ir.Output) }
          .unzip
        val paramNormalPorts = paramNormalPortss.flatten.toVector
        val paramFuturePorts = paramFuturePortss.flatten.toVector
        val paramPorts = paramNormalPorts ++ paramFuturePorts

        val activeInit = ir.Connect(ir.NoInfo, ir.Reference(activeName, ir.UnknownType), ir.UIntLiteral(0))
        val paramInits = paramNormalPorts.map(param => ir.IsInvalid(ir.NoInfo, ir.Reference(param.name, ir.UnknownType)))
        val future = paramFuturePorts.foldLeft(Future.empty) {
          case (acc, port) =>
            val ref = ir.Reference(port.name, ir.UnknownType)
            val future = Future(Map.empty, Map(ref -> UsageStyle.Field))

            acc + future
        }

        (future, activePort +: (paramPorts ++ retPorts), activeInit +: paramInits)
    }

    val (futures, ports, inits) = pairs.unzip3

    (futures.foldLeft(Future.empty)(_ + _), ports.flatten, inits.flatten)
  }

  def runStmt(stmt: backend.Stmt)(implicit stack: StackFrame, ctx: FirrtlContext, global: GlobalData): (Vector[ir.Statement], Future) = {
    def buildConnect(loc: ir.Expression, expr: backend.Expr): (Instance, Vector[ir.Statement], Future) = {
      val RunResult(exprFuture, stmts, instance) = runExpr(expr)

      val (retInst, connectFuture, connectOpt) = instance match {
        case _: ModuleInstance => (instance, Future.empty, Option.empty)
        case inst @ DataInstance(tpe, _) =>
          val (future, opt) = connect(loc, inst)
          val instance = DataInstance(tpe, loc)

          (instance, future, opt)
      }

      (retInst, stmts ++ connectOpt, exprFuture + connectFuture)
    }

    stmt match {
      case backend.Variable(name, tpe, expr) =>
        val varName = stack.next(name)
        val (normalWireOpt, futureWires) = wire(varName.name, tpe)
        val varRef = ir.Reference(varName.name, ir.UnknownType)

        val (inst, stmts, connectFuture) = buildConnect(varRef, expr)

        val future = futureWires.foldLeft(connectFuture) {
          case (acc, ir.DefWire(_, name, tpe)) =>
            val future = Future(Map.empty, Map(ir.Reference(name, ir.UnknownType) -> UsageStyle.Local(tpe)))
            acc + future
        }

        stack.append(varName, inst)
        ((normalWireOpt ++ stmts).toVector, future)
      case backend.Temp(id, expr) =>
        val tempName = stack.next(id)
        val RunResult(exprFuture, exprStmts, instance) = runExpr(expr)

        val (nodeInst, nodeFuture, nodeOpt) = instance match {
          case inst: ModuleInstance => (inst, Future.empty, Option.empty)
          case inst @ DataInstance(tpe, _) =>
            val (future, node) = defNode(tempName.name, inst)
            val retInst = DataInstance(tpe, ir.Reference(tempName.name, ir.UnknownType))

            (retInst, future, node)
        }

        val future = exprFuture + nodeFuture
        val stmts = exprStmts ++ nodeOpt

        stack.append(tempName, nodeInst)

        (stmts, future)
      case backend.Assign(target, expr) =>
        val loc = target.tail.foldLeft[ir.Expression](ir.Reference(target.head, ir.UnknownType)) {
          case (ref, name) => ir.SubField(ref, name, ir.UnknownType)
        }

        val (_, stmts, future) = buildConnect(loc, expr)
        (stmts, future)
      case backend.Abandon(expr) =>
        val RunResult(future, stmts, _) = runExpr(expr)
        (stmts, future)
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
      case backend.IntLiteral(value) => RunResult(Future.empty, Vector.empty, DataInstance(value))
      case backend.BoolLiteral(value) => RunResult(Future.empty, Vector.empty, DataInstance(value))
      case backend.UnitLiteral() => RunResult(Future.empty, Vector.empty, DataInstance())
      case bit @ backend.BitLiteral(value, HPElem.Num(width)) =>
        val future = Future.empty
        val stmts = Vector.empty
        val instance = StructInstance(bit.tpe, ir.UIntLiteral(value, ir.IntWidth(width)))
        RunResult(future, stmts, instance)
    }

  def runIdent(ident: backend.Ident)(implicit stack: StackFrame, ctx: FirrtlContext, global: GlobalData): RunResult = {
    val name = stack.refer(ident.id.name)
    RunResult(Future.empty, Vector.empty, stack.lookup(name))
  }

  def runReferField(referField: backend.ReferField)(implicit stack: StackFrame, ctx: FirrtlContext, global: GlobalData): RunResult = {
    val accessor = referField.accessor match {
      case backend.Term.Temp(id, _) => stack.lookup(stack.refer(id))
      case backend.Term.Variable(name, _) => stack.lookup(stack.refer(name))
    }

    val instance = accessor match {
      case DataInstance(_, refer) =>
        val subField = ir.SubField(refer, referField.field.toString, toFirrtlType(referField.tpe))
        StructInstance(referField.tpe, subField)
      case ModuleInstance(_, ModuleLocation.Sub(refer)) =>
        val subField = ir.SubField(refer, referField.field.toString, ir.UnknownType)
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
            val reference = ir.Reference(referField.field.toString, ir.UnknownType)
            ModuleInstance(tpe, ModuleLocation.Sub(reference))
          case _ =>
            val reference = ir.Reference(referField.field.toString, ir.UnknownType)
            StructInstance(tpe, reference)
        }
      case ModuleInstance(_, ModuleLocation.Upper(_)) =>
        throw new ImplementationErrorException("compiler does not support to refer upper module's field")
    }

    RunResult(Future.empty, Vector.empty, instance)
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
    val hargs = call.hargs.map {
      case HPElem.Num(value) => DataInstance(value)
      case HPElem.Str(value) => StringInstance(value)
    }

    val newStack = StackFrame(stack, accessor)

    val hargNames = method.hparams.keys.map(newStack.next)
    val argNames = method.params.keys.map(newStack.next)

    (hargNames zip hargs).foreach { case (name, harg) => newStack.append(name, harg) }
    (argNames zip args).foreach { case (name, arg) => newStack.append(name, arg) }

    val (stmtss, stmtFutures) = method.code.map(stmt => runStmt(stmt)(newStack, ctx, global)).unzip
    val RunResult(retFuture, retStmts, instance) = runExpr(method.ret)(newStack, ctx, global)

    val future = stmtFutures.foldLeft(retFuture)(_ + _)
    RunResult(future, stmtss.flatten ++ retStmts, instance)
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

    def calling(tpe: BackendType)(refer: String => ir.Expression): RunResult = {
      val candidates = ctx.interfaces(tpe)
      val interface = candidates.find(_.label == call.label).get

      val params = interface.params.toVector.map { case (name, _) => refer(name) }
      val argNames = call.args.map {
        case backend.Term.Temp(id, _) => stack.refer(id)
        case backend.Term.Variable(name, _) => stack.refer(name)
      }
      val args = argNames.map(stack.lookup).map(_.asInstanceOf[DataInstance])
      val activate = ir.Connect(ir.NoInfo, refer(interface.activeName), ir.UIntLiteral(1))

      val (futures, connectOpts) = (params zip args).map{ case (p, a) => connect(p, a) }.unzip
      val connects = connectOpts.flatten
      val future = futures.foldLeft(Future.empty)(_ + _)

      val returnedInstance = interface.ret match {
        case backend.UnitLiteral() => DataInstance()
        case _ => DataInstance(interface.retTpe, refer(interface.retName))
      }

      RunResult(future, activate +: connects, returnedInstance)
    }

    val referName = call.accessor match {
      case backend.Term.Temp(id, _) => stack.refer(id)
      case backend.Term.Variable(name, _) => stack.refer(name)
    }

    stack.lookup(referName) match {
      case ModuleInstance(tpe, ModuleLocation.This) => calling(tpe)(ir.Reference(_, ir.UnknownType))
      case ModuleInstance(tpe, ModuleLocation.Sub(refer)) => calling(tpe)(ir.SubField(refer, _, ir.UnknownType))
      case ModuleInstance(tpe, ModuleLocation.Upper(refer)) => calling(tpe)(name => ir.Reference(refer + "$" + name, ir.UnknownType))
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
      case "addInt" => builtin.intAdd(insts(0), insts(1))
      case "subInt" => builtin.intSub(insts(0), insts(1))
      case "mulInt" => builtin.intMul(insts(0), insts(1))
      case "divInt" => builtin.intDiv(insts(0), insts(1))
      case "orInt"  => builtin.intOr(insts(0), insts(1))
      case "andInt" => builtin.intAnd(insts(0), insts(1))
      case "xorInt" => builtin.intXor(insts(0), insts(1))
      case "shlInt" => builtin.intShl(insts(0), insts(1))
      case "shrInt" => builtin.intShr(insts(0), insts(1))
      case "dynShlInt" => builtin.intDynShl(insts(0), insts(1))
      case "dynShrInt" => builtin.intDynShr(insts(0), insts(1))
      case "eqInt" => builtin.intEq(insts(0), insts(1), global)
      case "neInt" => builtin.intNe(insts(0), insts(1), global)
      case "gtInt" => builtin.intGt(insts(0), insts(1), global)
      case "geInt" => builtin.intGe(insts(0), insts(1), global)
      case "ltInt" => builtin.intLt(insts(0), insts(1), global)
      case "leInt" => builtin.intLe(insts(0), insts(1), global)
      case "negInt" => builtin.intNeg(insts(0), global)
      case "notInt" => builtin.intNot(insts(0), global)
      case "orBool"  => builtin.boolOr(insts(0), insts(1))
      case "andBool" => builtin.boolAnd(insts(0), insts(1))
      case "xorBool" => builtin.boolXor(insts(0), insts(1))
      case "eqBool" => builtin.boolEq(insts(0), insts(1), global)
      case "neBool" => builtin.boolNe(insts(0), insts(1), global)
      case "notBool" => builtin.boolNot(insts(0), global)
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
      case "eqBit" => builtin.bitEq(insts(0), insts(1), global)
      case "neBit" => builtin.bitNe(insts(0), insts(1), global)
      case "gtBit" => builtin.bitGt(insts(0), insts(1), global)
      case "geBit" => builtin.bitGe(insts(0), insts(1), global)
      case "ltBit" => builtin.bitLt(insts(0), insts(1), global)
      case "leBit" => builtin.bitLe(insts(0), insts(1), global)
      case "negBit" => builtin.bitNeg(insts(0))
      case "notBit" => builtin.bitNot(insts(0))
      case "truncateBit" => builtin.bitTruncate(insts(0), call.hargs(0), call.hargs(1), global)
      case "bitBit" => builtin.bitBit(insts(0), call.hargs(0), global)
      case "concatBit" => builtin.bitConcat(insts(0), insts(1), global)
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

    val ModuleInstance(tpe, location) = stack.lookup(getName(read.accessor))
    val ModuleLocation.Sub(memory @ ir.Reference(memName, _)) = location
    val DataInstance(_, addrRef) = stack.lookup(getName(read.addr))

    def memSubField(head: String, name: String*): ir.SubField = {
      val subField = ir.SubField(memory, head, ir.UnknownType)
      name.foldLeft(subField) {
        case (accessor, name) => ir.SubField(accessor, name, ir.UnknownType)
      }
    }

    val port = s"read${read.port}"
    val enable = ir.Connect(ir.NoInfo, memSubField(port, "en"), ir.UIntLiteral(1))
    val addr = ir.Connect(ir.NoInfo, memSubField(port, "addr"), addrRef)

    val readDataName = ir.Reference(memName + "$" + s"_${port}_data", ir.UnknownType)
    val readingRegName = ir.Reference(memName + "$" + s"_reading0_${read.port}", ir.UnknownType)
    val readLatency = tpe.hargs(4)
    val readingConnect = readLatency match {
      case HPElem.Num(0) => ir.Connect(ir.NoInfo, ir.SubField(readDataName, "_member", ir.UnknownType), ir.UIntLiteral(1))
      case _ => ir.Connect(ir.NoInfo, readingRegName, ir.UIntLiteral(1))
    }

    val stmts = Vector(enable, addr, readingConnect)
    val future = BackendType(Symbol.future, Vector.empty, Vector(read.tpe))
    val instance = DataInstance(future, readDataName)

    RunResult(Future.empty, stmts, instance)
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

    def memSubField(head: String, name: String*): ir.SubField = {
      val subField = ir.SubField(memory, head, ir.UnknownType)
      name.foldLeft(subField) {
        case (accessor, name) => ir.SubField(accessor, name, ir.UnknownType)
      }
    }

    val port = s"write${write.port}"
    val enable = ir.Connect(ir.NoInfo, memSubField(port, "en"), ir.UIntLiteral(1))
    val addr = ir.Connect(ir.NoInfo, memSubField(port, "addr"), addrRef)
    val data = ir.Connect(ir.NoInfo, memSubField(port, "data"), dataRef)
    val stmts = Vector(enable, addr, data)
    val instance = DataInstance(BackendType(Symbol.unit, Vector.empty, Vector.empty), ir.UIntLiteral(0))

    RunResult(Future.empty, stmts, instance)
  }

  def runThis()(implicit stack: StackFrame, ctx: FirrtlContext, global: GlobalData): RunResult =
    RunResult(Future.empty, Vector.empty, stack.lookupThis.get)

  def runIfExpr(ifExpr: backend.IfExpr)(implicit stack: StackFrame, ctx: FirrtlContext, global: GlobalData): RunResult = {
    def runInner(stmts: Vector[backend.Stmt], last: backend.Expr): RunResult = {
      val (innerStmtss, innerFutures) = stmts.map(runStmt).unzip
      val RunResult(lastFuture, lastStmts, instance) = runExpr(last)

      val future = innerFutures.foldLeft(lastFuture)(_ + _)
      val allStmts = innerStmtss.flatten ++ lastStmts
      RunResult(future, allStmts, instance)
    }

    def buildCondition(condRef: ir.Expression): RunResult = {
      lazy val retName = stack.next("_IFRET")

      val (normalWireOpt, futureWires) = wire(retName.name, ifExpr.tpe)
      val retRef = ir.Reference(retName.name, ir.UnknownType)

      val RunResult(conseqFuture, conseqStmts, conseqInst: DataInstance) = runInner(ifExpr.conseq, ifExpr.conseqLast)
      val RunResult(altFuture, altStmts, altInst: DataInstance) = runInner(ifExpr.alt, ifExpr.altLast)
      val (conseqRetFuture, conseqRet) = connect(retRef, conseqInst)
      val (altRetFuture, altRet) = connect(retRef, altInst)

      val whenStmt = ir.Conditionally(
        ir.NoInfo,
        condRef,
        ir.Block(conseqStmts ++ conseqRet),
        ir.Block(altStmts ++ altRet)
      )

      val retInstance = ifExpr.tpe.symbol match {
        case symbol if symbol == Symbol.future => DataInstance()
        case _ => DataInstance(ifExpr.tpe, retRef)
      }

      val future = futureWires.foldLeft(conseqFuture + altFuture + conseqRetFuture + altRetFuture) {
        case (acc, wire) =>
          val ref = ir.Reference(wire.name, ir.UnknownType)
          val elem = ref -> UsageStyle.Local(wire.tpe)

          acc + Future(Map.empty, Map(elem))
      }

      val stmts = Vector(normalWireOpt, Some(whenStmt)).flatten

      RunResult(future, stmts, retInstance)
    }

    val condName = stack.refer(ifExpr.cond.id)
    stack.lookup(condName) match {
      case DataInstance(_, ir.UIntLiteral(cond, _)) if cond == 1 => runInner(ifExpr.conseq, ifExpr.conseqLast)
      case DataInstance(_, ir.UIntLiteral(cond, _)) if cond == 0 => runInner(ifExpr.alt, ifExpr.altLast)
      case DataInstance(_, condRef) => buildCondition(condRef)
    }
  }

  def runMatch(matchExpr: backend.Match)(implicit stack: StackFrame, ctx: FirrtlContext, global: GlobalData): RunResult = {
    def extractFieldData(source: ir.SubField, tpe: ir.Type, bitIdx: BigInt): (Vector[ir.Statement], Name, BigInt) =
      tpe match {
        case ir.UIntType(ir.IntWidth(width)) =>
          val name = stack.next("_EXTRACT")
          val expr = ir.DoPrim(PrimOps.Bits, Seq(source), Seq(bitIdx + width - 1, bitIdx), ir.UnknownType)
          val node = ir.DefNode(ir.NoInfo, name.name, expr)

          (Vector(node), name, bitIdx + width)
        case ir.BundleType(fields) =>
          val bundleName = stack.next("_EXTRACT")
          val wire = ir.DefWire(ir.NoInfo, bundleName.name, tpe)

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
        case ir.VectorType(tpe, length) =>
          val vecName = stack.next("_EXTRACT")
          val wire = ir.DefWire(ir.NoInfo, vecName.name, ir.VectorType(tpe, length))
          val wireRef = ir.Reference(wire.name, wire.tpe)

          val (stmts, nextIdx) = (0 to length).foldLeft(Vector.empty[ir.Statement], bitIdx){
            case ((stmts, bitIdx), idx) =>
              val (leafStmts, name, nextIdx) = extractFieldData(source, tpe, bitIdx)
              val connect = ir.Connect(
                ir.NoInfo,
                ir.SubIndex(wireRef, idx, ir.UnknownType),
                ir.Reference(name.name, ir.UnknownType)
              )

              (stmts ++ leafStmts :+ connect, nextIdx)
          }

          (wire +: stmts, vecName, nextIdx)
      }

    def runPattern(instance: DataInstance, pattern: backend.MatchPattern): (Vector[ir.Statement], DataInstance) = {
      def toFirrtlForm(lit: backend.Literal): ir.UIntLiteral = {
        def toLit(value: Int, width: Int): ir.UIntLiteral = ir.UIntLiteral(value, ir.IntWidth(width))

        lit match {
          case backend.IntLiteral(value) => toLit(value, 32)
          case backend.BitLiteral(value, HPElem.Num(width)) => toLit(value.toInt, width)
          case backend.BoolLiteral(value) => toLit(if(value) 1 else 0, 1)
          case backend.UnitLiteral() => toLit(0, 0)
        }
      }

      def literalPattern(lit: backend.Literal): (Vector[ir.Statement], DataInstance) = {
        val locName = stack.next("_GEN")
        val loc = ir.Reference(locName.name, ir.UnknownType)
        val locTpe = toBackendType(Type.boolTpe)
        val literal = toFirrtlForm(lit)
        val cmp = ir.DoPrim(PrimOps.Eq, Seq(instance.refer, literal), Seq.empty, ir.UnknownType)
        val node = ir.DefNode(ir.NoInfo, locName.name, cmp)
        val inst = DataInstance(locTpe, loc)

        (Vector(node), inst)
      }

      def identPattern(name: String): (Vector[ir.Statement], DataInstance) = {
        val locName = stack.next(name)
        val loc = ir.Reference(locName.name, ir.UnknownType)
        val node = ir.DefNode(ir.NoInfo, locName.name, instance.refer)
        val locInstance = DataInstance(instance.tpe, loc)
        stack.append(locName, locInstance)

        (Vector(node), DataInstance(bool = true))
      }

      pattern match {
        case backend.WildCardPattern(_) => (Vector.empty, DataInstance(bool = true))
        case backend.LiteralPattern(lit) => literalPattern(lit)
        case backend.IdentPattern(name) => identPattern(name.name)
        case backend.EnumPattern(variant, patterns, _) =>
          val memberRef = ir.SubField(instance.refer, "_member", ir.UnknownType)
          val dataRef = ir.SubField(instance.refer, "_data", ir.UnknownType)
          val variantEq = ir.DoPrim(PrimOps.Eq, Seq(memberRef, ir.UIntLiteral(variant)), Seq.empty, ir.UnknownType)

          val stmtBuilder = Vector.newBuilder[ir.Statement]
          val refBuilder = Vector.newBuilder[ir.Reference]
          patterns.map(_.tpe).scanLeft(BigInt(0)) {
            case (idx, tpe) =>
              val firrtlTpe = toFirrtlType(tpe)
              val (stmts, name, nextIdx) = extractFieldData(dataRef, firrtlTpe, idx)
              stmtBuilder ++= stmts
              refBuilder += ir.Reference(name.name, ir.UnknownType)

              nextIdx
          }

          val stmts = stmtBuilder.result()
          val refs = refBuilder.result()

          val trueRef = ir.UIntLiteral(1, ir.IntWidth(1))
          val (patternStmtss, conds) = (patterns zip refs)
            .map{ case (pattern, ref) => pattern -> DataInstance(pattern.tpe, ref) }
            .map{ case (pattern, inst) => runPattern(inst, pattern) }
            .unzip

          val condition = conds.filter(_.refer == trueRef).foldLeft[ir.Expression](variantEq) {
            case (left, right) => ir.DoPrim(PrimOps.And, Seq(left, right.refer), Seq.empty, ir.UnknownType)
          }

          val condName = stack.next("_GEN")
          val condRef = ir.Reference(condName.name, ir.UnknownType)
          val connect = ir.DefNode(ir.NoInfo, condName.name, condition)
          val returnStmts = stmts ++ patternStmtss.flatten :+ connect
          val boolTpe = toBackendType(Type.boolTpe)
          val returnInst = DataInstance(boolTpe, condRef)

          (returnStmts, returnInst)
      }
    }

    def runCase(instance: DataInstance, caseExpr: backend.Case, retLoc: Option[ir.Reference]): (Future, Vector[ir.Statement], ir.Conditionally) = {
      val (patternStmts, condInstance) = runPattern(instance, caseExpr.pattern)
      val (bodyStmtss, bodyFutures) = caseExpr.stmts.map(runStmt).unzip
      val bodyStmts = bodyStmtss.flatten
      val RunResult(exprFuture, exprStmts, retInstance: DataInstance) = runExpr(caseExpr.ret)

      val (retFuture, retConnect) = retLoc.map(loc => connect(loc, retInstance)).getOrElse(Future.empty, Option.empty)

      val conseqStmts = bodyStmts ++ exprStmts ++ retConnect

      val future = bodyFutures.foldLeft(retFuture + exprFuture)(_ + _)
      val cond = ir.Conditionally(ir.NoInfo, condInstance.refer, ir.Block(conseqStmts), ir.EmptyStmt)

      (future, patternStmts, cond)
    }

    val backend.Match(matched, cases, tpe) = matchExpr
    val instance = stack.lookup(stack.refer(matched.id))

    val retName = stack.next("_GEN")
    val (retWireOpt, retFutureWires) = wire(retName.name, tpe)
    val retRefOpt =
      if(tpe.symbol == Symbol.unit) None
      else Some(ir.Reference(retName.name, ir.UnknownType))
    val retInstance = retRefOpt.map(DataInstance(tpe, _)).getOrElse(DataInstance())
    val retInvalid = retWireOpt.map(wire => ir.IsInvalid(ir.NoInfo, ir.Reference(wire.name, ir.UnknownType)))
    val retStmts = Vector(retWireOpt, retInvalid).flatten

    stack.append(retName, retInstance)

    val (futures, patternStmtss, conds) = cases.map(runCase(instance.asInstanceOf[DataInstance], _, retRefOpt)).unzip3

    val retFutures = retFutureWires.map {
      case ir.DefWire(_, name, tpe) => ir.Reference(name, ir.UnknownType) -> UsageStyle.Local(tpe)
    }

    val future = futures.foldLeft(Future(Map.empty, retFutures.toMap))(_ + _)
    val patternStmts = patternStmtss.flatten
    val caseConds = conds.foldRight[ir.Statement](ir.Stop(ir.NoInfo, 1, clockRef, ir.UIntLiteral(1))) {
      case (cond, elsePart) =>  cond.copy(alt = elsePart)
    }

    val stmts = retStmts ++ patternStmts :+ caseConds

    RunResult(future, stmts, retInstance)
  }

  def runConstructStruct(construct: backend.ConstructStruct)(implicit stack: StackFrame, ctx: FirrtlContext, global: GlobalData): RunResult = {
    def constructData(preStmts: Vector[ir.Statement], results: Map[String, RunResult]): RunResult = {
      val bundleName = stack.next("_BUNDLE")
      val instance = DataInstance(construct.tpe, ir.Reference(bundleName.name, ir.UnknownType))
      stack.append(bundleName, instance)

      val bundleRef = ir.Reference(bundleName.name, ir.UnknownType)
      val (normalWireOpt, futureWires) = wire(bundleName.name, construct.tpe)
      val (futures, connectOpts) = results.mapValues(_.instance.asInstanceOf[DataInstance]).toVector.map{
        case (name, instance) =>
          val field = ir.SubField(bundleRef, name, ir.UnknownType)
          connect(field, instance)
      }.unzip
      val fieldFuture = futures.foldLeft(Future.empty)(_ + _)
      val connects = connectOpts.flatten
      val futureLocals = futureWires.map(wire => ir.Reference(wire.name, ir.UnknownType) -> UsageStyle.Local(wire.tpe))
      val localFuture = Future(Map.empty, futureLocals.toMap)

      val stmts = (normalWireOpt ++ connects).toVector
      val future = fieldFuture + localFuture

      RunResult(future, preStmts ++ stmts, instance)
    }

    val results = construct.pairs.map { case (key, value) => key -> runExpr(value) }
    val stmts = results.values.foldLeft(Vector.empty[ir.Statement]) {
      case (stmts, result) => stmts ++ result.stmts
    }

    constructData(stmts, results)
  }

  def runConstructModule(construct: backend.ConstructModule)(implicit stack: StackFrame, ctx: FirrtlContext, global: GlobalData): RunResult = {
    val moduleName = construct.name match {
      case backend.Term.Variable(name, _) => stack.lock(name); stack.refer(name)
      case backend.Term.Temp(id, _) => stack.next(id)
    }

    val moduleRef = ir.Reference(moduleName.name, ir.UnknownType)
    val instance = ModuleInstance(construct.tpe, ModuleLocation.Sub(ir.Reference(moduleName.name, ir.UnknownType)))
    stack.append(moduleName, instance)

    def buildIndirectAccessCond(interface: MethodContainer, fromName: String)(targetBuilder: String => ir.Expression): (Future, Option[ir.IsInvalid], ir.Conditionally) = {
      val isUnitRet = interface.ret.tpe.symbol == Symbol.unit

      def fromRef(name: String): ir.SubField = ir.SubField(moduleRef, fromName + "$" + name, ir.UnknownType)
      val fromActive = fromRef(interface.activeName)

      val (retFutureFrom, connectOpt) =
        if(isUnitRet) (Future.empty, Option.empty)
        else connect(fromRef(interface.retName), DataInstance(interface.retTpe, targetBuilder(interface.retName)))
      val retInvalid = connectOpt.map{ case ir.Connect(_, loc, _) => ir.IsInvalid(ir.NoInfo, loc) }
      val retFutureInit = Future(Map.empty, retFutureFrom.froms.keys.map(_ -> UsageStyle.Field).toMap)

      val params = interface.params.map{ case (name, _) => targetBuilder(name) }.toVector
      val args = interface.params.map{ case (name, tpe) => fromRef(name) -> tpe }.toVector
      val (futureConnects, connectOpts) = (params zip args).map{ case (param, (arg, tpe)) => connect(param, DataInstance(tpe, arg)) }.unzip
      val connects = connectOpts.flatten

      val activate = ir.Connect(ir.NoInfo, targetBuilder(interface.activeName), ir.UIntLiteral(1))
      val future = futureConnects.foldLeft(retFutureFrom + retFutureInit)(_ + _)

      val cond = ir.Conditionally(
        ir.NoInfo,
        fromActive,
        ir.Block(activate +: (connects ++ connectOpt)),
        ir.EmptyStmt
      )

      (future, retInvalid, cond)
    }

    val (parentFutures, parentStmtss, parentCondss) = construct.parents.map {
      case (fromName, expr) =>
        val RunResult(_, stmts, ModuleInstance(tpe, refer)) = runExpr(expr)
        val parents = ctx.interfaces(tpe).filter(_.label.symbol.hasFlag(Modifier.Parent))

        val targetName: String => ir.Expression = refer match {
          case ModuleLocation.This => (name: String) => ir.Reference(name, ir.UnknownType)
          case ModuleLocation.Upper(target) => name: String => ir.Reference(target + "$" + name, ir.UnknownType)
          case _: ModuleLocation.Sub => throw new ImplementationErrorException("refer a sub module as a parent module")
        }

        val (futures, invalids, conds) = parents.map(buildIndirectAccessCond(_, fromName)(targetName)).unzip3
        val future = futures.foldLeft(Future.empty)(_ + _)

        (future, stmts ++ invalids.flatten, conds)
    }.unzip3

    val (siblingFutures, siblingStmtss, siblingCondss) = construct.siblings.map {
      case (fromName, expr) =>
        val RunResult(_, stmts, ModuleInstance(tpe, refer)) = runExpr(expr)
        val siblings = ctx.interfaces(tpe).filter(_.label.symbol.hasFlag(Modifier.Sibling))

        val target: String => ir.Expression = refer match {
          case ModuleLocation.This => throw new ImplementationErrorException("refer this module as sibling module")
          case ModuleLocation.Sub(refer) => (name: String) => ir.SubField(refer, name, ir.UnknownType)
          case ModuleLocation.Upper(refer) => (name: String) => ir.Reference(refer + "$" + name, ir.UnknownType)
        }

        val (futures, invalid, conds) = siblings.map(buildIndirectAccessCond(_, fromName)(target)).unzip3
        val future = futures.foldLeft(Future.empty)(_ + _)

        (future, stmts ++ invalid.flatten, conds)
    }.unzip3

    val (inputFutures, inputInitss) = ctx.interfaces(construct.tpe)
      .filter(interface => interface.label.symbol.hasFlag(Modifier.Input) || interface.label.symbol.hasFlag(Modifier.Sibling))
      .map {
        interface =>
          def buildRef(name: String): ir.SubField = ir.SubField(moduleRef, name, ir.UnknownType)

          val activeRef = buildRef(interface.activeName)
          val (normalParamOpts, futureParamss) = interface.params.map{ case (name, tpe) => wire(name, tpe) }.unzip
          val normalParams = normalParamOpts.flatten.map(wire => buildRef(wire.name)).toVector
          val futureParams = futureParamss.flatten.map(wire => buildRef(wire.name)).toVector

          val activeOff = ir.Connect(ir.NoInfo, activeRef, ir.UIntLiteral(0))
          val paramInvalid = normalParams.map(ir.IsInvalid(ir.NoInfo, _))
          val futureElems = futureParams.map(_ -> UsageStyle.Field).toMap[ir.Expression, UsageStyle]

          val future = Future(Map.empty, futureElems)

          (future, activeOff +: paramInvalid)
      }
      .unzip

    val connectClock = ir.Connect(ir.NoInfo, ir.SubField(moduleRef, clockName, ir.UnknownType), clockRef)
    val connectReset = ir.Connect(ir.NoInfo, ir.SubField(moduleRef, resetName, ir.UnknownType), resetRef)
    val parentStmts = parentStmtss.toVector.flatten
    val siblingStmts = siblingStmtss.toVector.flatten
    val inputStmts = inputInitss.flatten
    val conds = (siblingCondss.toVector ++ parentCondss.toVector).flatten
    val future = (parentFutures ++ siblingFutures ++ inputFutures).foldLeft(Future.empty)(_ + _)

    val stmts = Vector(connectClock, connectReset) ++ inputStmts ++ parentStmts ++ siblingStmts ++ conds

    RunResult(future, stmts, instance)
  }

  def runConstructMemory(memory: backend.ConstructMemory)(implicit stack: StackFrame, ctx: FirrtlContext, global: GlobalData): RunResult = {
    val refer = memory.name match {
      case backend.Term.Variable(name, _) => ir.Reference(name, ir.UnknownType)
      case backend.Term.Temp(id, _) => ir.Reference(stack.refer(id).name, ir.UnknownType)
    }

    val instance = ModuleInstance(memory.tpe, ModuleLocation.Sub(refer))

    RunResult(Future.empty, Vector.empty, instance)
  }

  def runConstructEnum(enum: backend.ConstructEnum)(implicit stack: StackFrame, ctx: FirrtlContext, global: GlobalData): RunResult = {
    def makeLeafs(tpe: ir.Type, refer: ir.Expression): Vector[ir.Expression] = {
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
    }

    val tpe = toFirrtlType(enum.target)
    val insts = enum.passed.map(temp => stack.lookup(stack.refer(temp.id)))

    val value = insts
      .map(_.asInstanceOf[DataInstance])
      .flatMap(inst => makeLeafs(toFirrtlType(inst.tpe), inst.refer))
      .reduceLeftOption[ir.Expression] { case (prefix, refer) => ir.DoPrim(PrimOps.Cat, Seq(refer, prefix), Seq.empty, ir.UnknownType) }
      .getOrElse(ir.UIntLiteral(0))

    val flagValue = enum.tpe.symbol.tpe.declares
      .toMap.toVector
      .sortWith { case ((left, _), (right, _)) => left < right }
      .map { case (_, symbol) => symbol }
      .zipWithIndex
      .find { case (symbol, _) => symbol == enum.variant }
      .map { case (_, idx) => ir.UIntLiteral(idx) }
      .getOrElse(throw new ImplementationErrorException(s"${enum.variant} was not found"))

    val enumName = stack.next("_ENUM")
    val enumRef = ir.Reference(enumName.name, ir.UnknownType)
    val wireDef =
      if (enum.target.symbol == Symbol.future) None
      else Some(ir.DefWire(ir.NoInfo, enumName.name, tpe))

    val connectFlag = ir.Connect(
      ir.NoInfo,
      ir.SubField(enumRef, "_member", ir.UnknownType),
      flagValue
    )
    val connectData = ir.Connect(
      ir.NoInfo,
      ir.SubField(enumRef, "_data", ir.UnknownType),
      value
    )

    val runResultStmts = (wireDef ++ Vector(connectFlag, connectData)).toVector
    val instance = DataInstance(enum.tpe, enumRef)

    val future =
      if (enum.target.symbol != Symbol.future) Future(Map.empty, Map.empty)
      else Future(Map.empty, Map(enumRef -> UsageStyle.Constructor(tpe)))

    RunResult(future, runResultStmts, instance)
  }

  def runFinish(finish: backend.Finish)(implicit stack: StackFrame, ctx: FirrtlContext, global: GlobalData): RunResult = {
    val active = finish.stage.activeName
    val activeRef = ir.Reference(active, ir.UnknownType)
    val finishStmt = ir.Connect(ir.NoInfo, activeRef, ir.UIntLiteral(0))

    RunResult(Future.empty, Vector(finishStmt), DataInstance())
  }

  def runGoto(goto: backend.Goto)(implicit stack: StackFrame, ctx: FirrtlContext, global: GlobalData): RunResult = {
    val stage = goto.state.label.stage
    val state = goto.state.label
    val stageContainer = ctx.stages(stack.lookupThis.get.tpe).find(_.label == stage).get
    val stateContainer = stageContainer.states.find(_.label == state).get

    val stateRef = ir.Reference(stage.stateName, ir.UnknownType)
    val changeState = ir.Connect(ir.NoInfo, stateRef, ir.UIntLiteral(state.index))

    val (future, stmts) = assignRegParams(stateContainer.params, goto.state.args)

    RunResult(future, changeState +: stmts, DataInstance())
  }

  def runGenerate(generate: backend.Generate)(implicit stack: StackFrame, ctx: FirrtlContext, global: GlobalData): RunResult = {
    val stageContainer = ctx.stages(stack.lookupThis.get.tpe).find(_.label == generate.stage).get
    val activeRef = ir.Reference(generate.stage.activeName, ir.UnknownType)
    val activate = Vector(ir.Connect(ir.NoInfo, activeRef, ir.UIntLiteral(1)))
    val state = generate.state match {
      case None => Vector.empty
      case Some(backend.State(label, _)) =>
        Vector(ir.Connect(
          ir.NoInfo,
          ir.Reference(stageContainer.label.stateName, ir.UnknownType),
          ir.UIntLiteral(label.index)
        ))
    }

    val (stageFuture, stageAssigns) = assignRegParams(stageContainer.params, generate.args)
    val (stateFuture, stateAssigns) = generate.state.map {
      state =>
        val backend.State(stateLabel, args) = state
        val stateContainer = stageContainer.states.find(_.label.index == stateLabel.index).get

        assignRegParams(stateContainer.params, args)
    }.getOrElse(Future.empty, Vector.empty)

    val stmts = activate ++ state ++ stageAssigns ++ stateAssigns
    val future = stageFuture + stateFuture

    val retInstance =
      if (stageContainer.ret.symbol == Symbol.unit) DataInstance()
      else DataInstance(stageContainer.ret, ir.Reference(stageContainer.retName, ir.UnknownType))

    RunResult(future, stmts, retInstance)
  }

  private def assignRegParams(params: ListMap[String, BackendType], args: Vector[backend.Term.Temp])(implicit stack: StackFrame, ctx: FirrtlContext, global: GlobalData): (Future, Vector[ir.Statement]) = {
    val instances = args.map{ case backend.Term.Temp(id, _) => stack.refer(id) }.map(stack.lookup).map(_.asInstanceOf[DataInstance])
    val paramRefs = params.map{ case (name, _) => ir.Reference(name, ir.UnknownType) }

    val (connectFutures, connectOpts) = (paramRefs zip instances).map{ case (p, a) => connect(p, a) }.unzip
    val connects = connectOpts.flatten.toVector
    val future = connectFutures.foldLeft(Future.empty)(_ + _)


    /*
    val (futureStateParams, normalStateParams) = params.partition { case (_, tpe) => tpe.symbol == Symbol.future }
    val (futureStateArgs, normalStateArgs) = args.partition { case backend.Term.Temp(_, tpe) => tpe.symbol == Symbol.future }

    val normalAssigns = (normalStateParams zip normalStateArgs)
      .map { case ((param, _), backend.Term.Temp(id, _)) => param -> stack.refer(id).name }
      .map { case (param, arg) => param -> ir.Reference(arg, ir.UnknownType) }
      .map { case (param, arg) => ir.Connect(ir.NoInfo, ir.Reference(param, ir.UnknownType), arg) }
      .toVector

    val futureAssigns = (futureStateParams zip futureStateArgs)
      .map { case ((param, _), arg) => ir.Reference(param, ir.UnknownType) -> arg }
      .map { case (param, backend.Term.Temp(id, _)) => param -> stack.refer(id).name }
      .map { case (param, arg) => param -> ir.Reference(arg, ir.UnknownType) }
      .map { case (param, arg) => param -> Vector(arg) }
      .toMap[ir.Expression, Vector[ir.Expression]]

    val future = Future(futureAssigns, Map.empty)
    */

    (future, connects)
  }

  def runReturn(ret: backend.Return)(implicit stack: StackFrame, ctx: FirrtlContext, global: GlobalData): RunResult = {
    val RunResult(exprFuture, stmts, instance) = runExpr(ret.expr)
    val loc = ir.Reference(ret.stage.retName, ir.UnknownType)
    val DataInstance(_, refer) = instance
    val retFuture = Future(Map(loc -> Vector(refer)), Map.empty)

    RunResult(exprFuture + retFuture, stmts, DataInstance())
  }

  private def connect(loc: ir.Expression, from: DataInstance)(implicit stack: StackFrame, global: GlobalData): (Future, Option[ir.Connect]) = {
    def flattenName(ref: ir.Expression): (Option[ir.Expression], String) = ref match {
      case ir.Reference(name, _) => (None, name)
      case ir.SubField(ref @ ir.Reference(name, _), field, _) =>
        stack.lookup(Name(name)) match {
          case _: DataInstance => (None, name + "_" + field)
          case _: ModuleInstance => (Some(ref), field)
        }
      case ir.SubField(expr, name, _) =>
        val (head, suffix) = flattenName(expr)
        (head, suffix + "_" + name)
      // if ir.SubIndex or ir.SubAccess, it is vector type.
      // Vector type also does not allow types contains future,
      // so if this pattern match catches ir.SubIndex or ir.SubAccess,
      // this connection will not treat Future anywhere and does not need appropriate names.
      case _ => (None, "")
    }

    def futureRefs(tpe: BackendType, name: String): Map[String, String => String] = {
      tpe.symbol match {
        case sym if sym == Symbol.future => Map(name -> (_ + name))
        case _ => tpe.fields.flatMap{ case (last, tpe) => futureRefs(tpe, name + "_" + last) }
      }
    }

    def futureConnect(froms: Vector[(String, ir.Expression)], locs: Vector[(String, ir.Expression)]): Vector[(ir.Expression, ir.Expression)] = {
      froms.headOption match {
        case None => Vector.empty
        case Some(from) =>
          val (loc, remains) = locs.findRemain{ case (name, _) => name == from._1 }
          (loc.get._2, from._2) +: futureConnect(froms.tail, remains)
      }
    }

    def attachPrefix(prefix: Option[ir.Expression], suffix: String): ir.Expression =
      prefix match {
        case Some(ref) => ir.SubField(ref, suffix, ir.UnknownType)
        case None => ir.Reference(suffix, ir.UnknownType)
      }

    val (fromPrefix, fromName) = flattenName(from.refer)
    val (locPrefix, locName) = flattenName(loc)
    val refs = futureRefs(from.tpe, "")
    val fromFutureNames = refs.mapValues(f => f(fromName))
    val locFutureNames = refs.mapValues(f => f(locName))
    val fromFutureRefs = fromFutureNames.map{ case (key, name) => key -> attachPrefix(fromPrefix, name) }
    val locFutureRefs = locFutureNames.map{ case (key, name) => key -> attachPrefix(locPrefix, name) }

    val futures = futureConnect(fromFutureRefs.toVector, locFutureRefs.toVector)
    val future = Future(futures.map{ case (loc, from) => loc -> Vector(from) }.toMap, Map.empty)
    val connect =
      if(from.tpe.symbol == Symbol.future) None
      else Some(ir.Connect(ir.NoInfo, loc, from.refer))

    (future, connect)
  }

  private def defNode(loc: String, from: DataInstance)(implicit stack: StackFrame, global: GlobalData): (Future, Option[ir.DefNode]) = {
    def futureRefs(tpe: BackendType, name: String): Map[ir.Expression, UsageStyle] = {
      tpe.symbol match {
        case sym if sym == Symbol.future => Map(ir.Reference(name, ir.UnknownType) -> UsageStyle.Local(tpe.toFirrtlType))
        case _ => tpe.fields.flatMap{ case (last, tpe) => futureRefs(tpe, name + "_" + last) }
      }
    }

    val (future, connectOpt) = connect(ir.Reference(loc, ir.UnknownType), from)
    val node = connectOpt.map{ case ir.Connect(_, _, expr) => ir.DefNode(ir.NoInfo, loc, expr) }
    val refFuture = Future(Map.empty, futureRefs(from.tpe, loc))

    (future + refFuture, node)
  }

  private def definition[A <: ir.FirrtlNode, B <: ir.FirrtlNode](normalBuilder: (String, ir.Type) => A, futureBuilder: (String, ir.Type) => B)(name: String, tpe: BackendType)(implicit global: GlobalData): (Option[A], Vector[B]) = {
    def futureNames(tpe: BackendType, name: String): Vector[(String, BackendType)] = {
      tpe.symbol match {
        case sym if sym == Symbol.future => Vector(name -> tpe)
        case _ => tpe.fields.flatMap{ case (last, tpe) => futureNames(tpe, name + "_" + last) }.toVector
      }
    }

    def removeFuture(tpe: BackendType): Option[ir.Type] = {
      if(tpe.symbol == Symbol.future) None
      else tpe.symbol match {
        case symbol if symbol == Symbol.int => Some(ir.UIntType(ir.IntWidth(32)))
        case symbol if symbol == Symbol.bool => Some(ir.UIntType(ir.IntWidth(1)))
        case symbol if symbol == Symbol.unit => Some(ir.UIntType(ir.IntWidth(0)))
        case symbol if symbol == Symbol.bit => Some(tpe.toFirrtlType)
        case symbol if symbol == Symbol.future => None
        case _: Symbol.EnumSymbol => Some(tpe.toFirrtlType)
        case symbol if symbol == Symbol.vec => Some(tpe.toFirrtlType)
        case _ =>
          val fields = tpe.fields
            .map{ case (name, tpe) => name -> removeFuture(tpe) }
            .collect{ case (name, Some(tpe)) => name -> tpe }
            .toVector
            .sortWith{ case ((left, _), (right, _)) => left < right }
            .map{ case (name, tpe) => ir.Field(name, ir.Default, tpe) }

          if(fields.isEmpty) None
          else Some(ir.BundleType(fields))
      }
    }

    val futures = futureNames(tpe, name)
    val futureComponents = futures.map{ case (name, tpe) => futureBuilder(name, tpe.toFirrtlType) }
    val normalComponent = Option(tpe)
      .filter(_.symbol != Symbol.unit)
      .flatMap(removeFuture(_).map(tpe => normalBuilder(name, tpe)))

    (normalComponent, futureComponents)
  }

  private def wire(name: String, tpe: BackendType)(implicit global: GlobalData): (Option[ir.DefWire], Vector[ir.DefWire]) = {
    val wireBuilder = (name: String, tpe: ir.Type) => ir.DefWire(ir.NoInfo, name, tpe)
    definition(wireBuilder, wireBuilder)(name, tpe)
  }

  private def register(name: String, tpe: BackendType)(implicit global: GlobalData): (Option[ir.DefRegister], Vector[ir.DefWire]) = {
    val regBuilder = (name: String, tpe: ir.Type) => ir.DefRegister(ir.NoInfo, name, tpe, clockRef, resetRef, ir.Reference(name, ir.UnknownType))
    val wireBuilder = (name: String, tpe: ir.Type) => ir.DefWire(ir.NoInfo, name, tpe)

    definition(regBuilder, wireBuilder)(name, tpe)
  }

  private def port(name: String, tpe: BackendType, flow: ir.Direction)(implicit global: GlobalData): (Option[ir.Port], Vector[ir.Port]) = {
    val portBuilder = (name: String, tpe: ir.Type) => ir.Port(ir.NoInfo, name, flow, tpe)

    definition(portBuilder, portBuilder)(name, tpe)
  }
}
