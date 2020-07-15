package tchdl.backend

import tchdl.backend.{ast => backend}
import tchdl.util._
import tchdl.util.TchdlException._
import firrtl.{PrimOps, ir}

import scala.annotation.tailrec
import scala.collection.immutable.ListMap
import scala.collection.mutable

object FirrtlCodeGen {
  val clockName = "_CLK"
  val resetName = "_RESET"
  val clockRef = ir.Reference(clockName, ir.ClockType)
  val resetRef = ir.Reference(resetName, ir.UIntType(ir.IntWidth(1)))

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

      if(parent != null)
        parent.count(name)

      refer(name)
    }

    def next(id: Int): Name = {
      namer.temp.next(id)

      if(parent != null)
        parent.count(id)

      refer(id)
    }

    def refer(name: String): Name = namer.variable.refer(name)
    def refer(id: Int): Name = namer.temp.refer(id)

    def lock(name: String): Unit = namer.variable.lock(name)

    @tailrec private def count(name: String): Unit = {
      namer.variable.count(name)

      if(parent != null)
        parent.count(name)
    }

    @tailrec private def count(id: Int): Unit = {
      namer.temp.count(id)

      if(parent != null)
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

      Name(s"TEMP_$nextMax")
    }

    def count(key: Int): Unit = {
      max = max + 1
    }

    def refer(key: Int): Name = {
      val value = table(key)
      Name(s"TEMP_$value")
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

      table.get(key) orElse eachMax.get(key) match {
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

    def lock(key: String): Unit = { locked += key }

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
    val interfaceTable = modules.map(module => module.tpe -> module.interfaces).toMap
    val stageTable = modules.map(module => module.tpe -> module.stages).toMap
    val methodTable = methods
      .collect{ case method if method.label.accessor.isDefined => method }
      .groupBy(_.label.accessor.get)
    val functionTable = methods.collect{ case method if method.label.accessor.isEmpty => method }

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

    module.hps
      .map { case (name, elem) => stack.next(name) -> elem }
      .foreach {
        case (name, HPElem.Num(num)) => stack.append(name, DataInstance(num))
        case (name, HPElem.Str(str)) => stack.append(name, StringInstance(str))
      }

    val (inputStmts, inputs, inputFutures) = module.fields
      .filter(_.flag.hasFlag(Modifier.Input))
      .map(runInput(_)(stack, ctx, global))
      .unzip3

    val (outputStmts, outputs, outputFutures) = module.fields
      .filter(_.flag.hasFlag(Modifier.Output))
      .map(runOutput(_)(stack, ctx, global))
      .unzip3

    val (internalStmts, internals, internalFutures) = module.fields
      .filter(_.flag.hasFlag(Modifier.Internal))
      .map(runInternal(_)(stack, ctx, global))
      .unzip3

    val (regStmts, registers, regFutures) = module.fields
      .filter(_.flag.hasFlag(Modifier.Register))
      .map(runRegister(_)(stack, ctx, global))
      .unzip3

    val (moduleFutures, moduleStmts, moduleConds, modules) = module.fields
      .filter(_.flag.hasFlag(Modifier.Child))
      .map(runSubModule(_)(stack, ctx, global))
      .unzip4

    val clk = ir.Port(ir.NoInfo, clockName, ir.Input, ir.ClockType)
    val reset = ir.Port(ir.NoInfo, resetName, ir.Input, ir.UIntType(ir.IntWidth(1)))
    val ports = Vector(clk, reset) ++ inputs ++ outputs
    val initStmts = (inputStmts ++ outputStmts ++ internalStmts ++ regStmts ++ moduleStmts ++ moduleConds).flatten
    val components = internals ++ registers ++ modules

    val (alwaysStmtss, alwaysFutures) = module.always.map(runAlways(_)(stack, ctx, global)).unzip
    val alwaysStmts = alwaysStmtss.flatten
    val (futurePorts, interfacePorts, interfaceStmts, interfaceFutures) = module.interfaces.map(buildInterfaceSignature(_)(stack, global)).unzip4
    val (interfaceConds, interfaceCondFutures) = module.interfaces.map(runInterface(_)(stack, ctx, global)).unzip
    val (futureSigss, stageStmtss, stageFutures) = module.stages.map(buildStageSignature(_)(stack, ctx, global)).unzip3
    val stageStmts = stageStmtss.flatten
    val (stageConds, stageCondFutures) = module.stages.map(runStage(_)(stack, ctx, global)).unzip
    val moduleField = global.lookupFields(module.tpe)
    val (upperFutures, upperPorts, upperPortInits) = moduleField.map{ case (name, tpe) => buildUpperModule(name, tpe)(ctx, global) }.toVector.unzip3

    val (futureInterfacePortss, futureInterfaceWiress) = futurePorts.map {
      case Left(ports) => (ports, Vector.empty)
      case Right(wires) => (Vector.empty, wires)
    }.unzip

    val futureInterfacePorts = futureInterfacePortss.flatten
    val futureInterfaceWires = futureInterfaceWiress.flatten
    val futureSigs = futureSigss.flatten

    val futures =
      moduleFutures ++
      upperFutures ++
      inputFutures ++
      outputFutures ++
      internalFutures ++
      regFutures ++
      alwaysFutures ++
      interfaceFutures ++
      interfaceCondFutures ++
      stageFutures ++
      stageCondFutures

    val futureStmts = buildFuture(futures.foldLeft(Future.empty)(_ + _))

    ir.Module(
      ir.NoInfo,
      module.tpe.toFirrtlString,
      ports ++ futureInterfacePorts ++ interfacePorts.flatten ++ upperPorts.flatten,
      ir.Block(interfaceStmts.flatten ++ upperPortInits.flatten ++ futureInterfaceWires ++ components ++ initStmts ++ futureSigs ++ futureStmts ++ stageStmts ++ alwaysStmts ++ interfaceConds ++ stageConds)
    )
  }

  def runInput(field: FieldContainer)(implicit stack: StackFrame, ctx: FirrtlContext, global: GlobalData): (Vector[ir.Statement], ir.Port, Future) = {
    val (stmtss, futures) = field.code.map(runStmt).unzip
    val retExpr = field.ret.map(throw new ImplementationErrorException("input wire with init expression is not supported yet"))
    val firrtlType = toFirrtlType(field.tpe)

    val port = ir.Port(ir.NoInfo, field.toFirrtlString, ir.Input, firrtlType)

    val future = futures.foldLeft(Future.empty)(_ + _)

    (stmtss.flatten, port, future)
  }

  def runOutput(field: FieldContainer)(implicit stack: StackFrame, ctx: FirrtlContext, global: GlobalData): (Vector[ir.Statement], ir.Port, Future) = {
    val (stmtss, futures) = field.code.map(runStmt).unzip
    val fieldRef = ir.Reference(field.toFirrtlString, ir.UnknownType)
    val (retFuture, retStmt) = field.ret.map(runExpr) match {
      case Some(RunResult(future, stmts, DataInstance(_, refer))) => (future, stmts :+ ir.Connect(ir.NoInfo, fieldRef, refer))
      case None => (Future.empty, Vector.empty)
    }

    val future = futures.foldLeft(retFuture)(_ + _)
    val tpe = toFirrtlType(field.tpe)
    val port = ir.Port(ir.NoInfo, field.toFirrtlString, ir.Output, tpe)

    (stmtss.flatten ++ retStmt, port, future)
  }

  def runInternal(field: FieldContainer)(implicit stack: StackFrame, ctx: FirrtlContext, global: GlobalData): (Vector[ir.Statement], ir.DefWire, Future) = {
    val (stmtss, stmtFutures) = field.code.map(runStmt).unzip
    val fieldRef = ir.Reference(field.toFirrtlString, ir.UnknownType)
    val (retFuture, retStmt) = field.ret
      .map(runExpr)
      .map{ case RunResult(future, stmts, DataInstance(_, refer)) => (future, stmts, refer) }
      .map{ case (future, stmts, refer) => (future, stmts :+ ir.Connect(ir.NoInfo, fieldRef, refer)) }
      .getOrElse((Future.empty, Vector(ir.IsInvalid(ir.NoInfo, fieldRef))))
    val tpe = toFirrtlType(field.tpe)
    val wire = ir.DefWire(ir.NoInfo, field.toFirrtlString, tpe)

    val future = stmtFutures.foldLeft(retFuture)(_ + _)

    (stmtss.flatten ++ retStmt, wire, future)
  }

  def runRegister(field: FieldContainer)(implicit stack: StackFrame, ctx: FirrtlContext, global: GlobalData): (Vector[ir.Statement], ir.DefRegister, Future) = {
    val (stmtss, futures) = field.code.map(runStmt).unzip
    val fieldRef = ir.Reference(field.toFirrtlString, ir.UnknownType)
    val (retFuture, retStmts, retExpr) = field.ret
      .map(runExpr)
      .map{ case RunResult(retFuture, stmts, DataInstance(_, refer)) => (retFuture, stmts, refer) }
      .getOrElse((Future.empty, Vector.empty, fieldRef))
    val tpe = toFirrtlType(field.tpe)
    val reg = ir.DefRegister(ir.NoInfo, field.toFirrtlString, tpe, clockRef, resetRef, retExpr)

    val future = futures.foldLeft(retFuture)(_ + _)

    (stmtss.flatten ++ retStmts, reg, future)
  }

  def runSubModule(field: FieldContainer)(implicit stack: StackFrame, ctx: FirrtlContext, global: GlobalData): (Future, Vector[ir.Statement], Vector[ir.Conditionally], ir.DefInstance) = {
    val (stmtss, _) = field.code.map(runStmt).unzip
    val (future, retStmts) = field.ret
      .map(runExpr)
      .map{ case RunResult(future, stmts, _) => (future, stmts) }
      .getOrElse(throw new ImplementationErrorException("sub module instance expression must be there"))

    val tpeString = field.tpe.toFirrtlString
    val module = ir.DefInstance(ir.NoInfo, field.toFirrtlString, tpeString)

    val subModuleStmts = stmtss.flatten ++ retStmts
    val (conds, others) = subModuleStmts.collectPartition{ case cond: ir.Conditionally => cond }

    (future, others, conds, module)
  }

  def runAlways(always: AlwaysContainer)(implicit stack: StackFrame, ctx: FirrtlContext, global: GlobalData): (Vector[ir.Statement], Future) = {
    val (stmtss, futures) = always.code.map(runStmt).unzip

    (stmtss.flatten, futures.foldLeft(Future.empty)(_ + _))
  }

  def buildStageSignature(stage: StageContainer)(implicit stack: StackFrame, ctx: FirrtlContext, global: GlobalData): (Vector[ir.DefWire], Vector[ir.Statement], Future) = {
    stage.params.foreach { case (name, _) => stack.lock(name) }
    val args = stage.params
      .map{ case (name, tpe) => stack.refer(name) -> tpe }
      .map{ case (name, tpe) => name -> StructInstance(tpe, ir.Reference(name.name, ir.UnknownType)) }
      .toVector

    args.foreach { case (name, instance) => stack.append(name, instance) }

    val (futureArgs, normalArgs) = args.partition { case (_, DataInstance(tpe, _)) => tpe.symbol == Symbol.future }

    val active = ir.DefRegister(
      ir.NoInfo,
      stage.activeName,
      ir.UIntType(ir.IntWidth(1)),
      clockRef,
      resetRef,
      ir.UIntLiteral(0)
    )

    def log2(x: Double): Double = math.log10(x) / math.log10(2.0)
    def stateWidth(x: Double): Double = (math.ceil _ compose log2)(x)

    val state =
      if(stage.states.length <= 1) None
      else Some(ir.DefRegister (
        ir.NoInfo,
        stage.stateName,
        ir.UIntType(ir.IntWidth(stateWidth(stage.states.length).toInt)),
        clockRef,
        resetRef,
        ir.UIntLiteral(0)
      ))

    val regs = normalArgs.map {
      case (name, instance) =>
        ir.DefRegister(
          ir.NoInfo,
          name.name,
          toFirrtlType(instance.tpe),
          clockRef,
          resetRef,
          ir.Reference(name.name, ir.UnknownType)
        )
    }

    val ret =
      if(stage.ret == toBackendType(Type.unitTpe)) None
      else Some(ir.DefWire(ir.NoInfo, stage.retName, toFirrtlType(stage.ret)))

    val retRef = ir.Reference(stage.retName, ir.UnknownType)
    val futureRet =
      if(stage.ret == toBackendType(Type.unitTpe)) Future(Map.empty, Map.empty)
      else Future(Map.empty, Map(retRef -> FormKind.Stage))

    val futureElems = futureArgs
      .map { case (name, _) => ir.Reference(name.name, ir.UnknownType) }
      .map { _ -> FormKind.Stage }
      .toMap[ir.Expression, FormKind]

    val wires = futureArgs.map{ case (name, instance) => ir.DefWire(ir.NoInfo, name.name, toFirrtlType(instance.tpe)) }

    val future = Future(Map.empty, futureElems)

    ((ret ++ wires).toVector, active +: (regs ++ Vector(state).flatten), future + futureRet)
  }

  def runStage(stage: StageContainer)(implicit stack: StackFrame, ctx: FirrtlContext, global: GlobalData): (ir.Conditionally, Future) = {
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
    (cond, future)
  }

  def buildInterfaceSignature(interface: MethodContainer)(implicit stack: StackFrame, global: GlobalData): (Either[Vector[ir.Port], Vector[ir.DefWire]], Vector[ir.Port], Vector[ir.Statement], Future) = {
    interface.params.foreach { case (name, _) => stack.lock(name) }
    val args = interface.params
      .map{ case (name, tpe) => stack.refer(name) -> tpe }
      .map{ case (name, tpe) => name -> DataInstance(tpe, ir.Reference(name.name, ir.UnknownType)) }
      .toVector

    args.foreach { case (name, instance) => stack.append(name, instance) }

    val isInputInterface =
      interface.label.symbol.hasFlag(Modifier.Input) ||
      interface.label.symbol.hasFlag(Modifier.Sibling)

    val normalParams = args.filter{ case (_, DataInstance(tpe, _)) => tpe.symbol != Symbol.future }
    val futureParams = args.filter{ case (_, DataInstance(tpe, _)) => tpe.symbol == Symbol.future }

    val normalParamWires =
      if(isInputInterface) normalParams.map{ case (name, inst) => ir.Port(ir.NoInfo, name.name, ir.Input, toFirrtlType(inst.tpe))}
      else normalParams.map{ case (name, inst) => ir.DefWire(ir.NoInfo, name.name, toFirrtlType(inst.tpe)) }

    val futureParamWires =
      if(isInputInterface) futureParams.map{ case (name, inst) => ir.Port(ir.NoInfo, name.name, ir.Input, toFirrtlType(inst.tpe))}
      else futureParams.map{ case (name, inst) => ir.DefWire(ir.NoInfo, name.name, toFirrtlType(inst.tpe)) }

    val paramInvalids =
      if(isInputInterface) Vector.empty
      else args
        .filter{ case (_, DataInstance(tpe, _)) => tpe.symbol != Symbol.future }
        .map{ case (name, _) => ir.IsInvalid(ir.NoInfo, ir.Reference(name.name, ir.UnknownType)) }

    val active =
      if(isInputInterface) ir.Port(ir.NoInfo, interface.activeName, ir.Input, ir.UIntType(ir.IntWidth(1)))
      else ir.DefWire(ir.NoInfo, interface.activeName, ir.UIntType(ir.IntWidth(1)))

    val activeOff =
      if(isInputInterface) None
      else Some(ir.Connect(ir.NoInfo, ir.Reference(interface.activeName, ir.UnknownType), ir.UIntLiteral(0)))

    val retTpe = interface.label.symbol.tpe.asMethodType.returnType
    val isUnitRet = retTpe == Type.unitTpe
    val isFutureRet = retTpe.origin == Symbol.future

    val retPort = ir.Port(ir.NoInfo, interface.retName, ir.Output, toFirrtlType(interface.retTpe))
    val retWire = ir.DefWire(ir.NoInfo, interface.retName, toFirrtlType(interface.retTpe))

    val normalRet =
      if (isUnitRet || isFutureRet) None
      else if(isInputInterface) Some(retPort)
      else Some(retWire)

    val futureRet =
      if(isFutureRet && isInputInterface) Some(retPort)
      else if(isFutureRet) Some(retWire)
      else None

    val retRef = ir.Reference(interface.retName, ir.UnknownType)

    val retInit =
      if(isUnitRet || isFutureRet) None
      else Some(ir.IsInvalid(ir.NoInfo, retRef))

    val retFuture =
      if(isFutureRet) Future(Map.empty, Map(retRef -> FormKind.Field))
      else Future.empty

    if(isInputInterface) {
      val futurePorts = futureParamWires.map(_.asInstanceOf[ir.Port])
      val futureRetPort = futureRet.map(_.asInstanceOf[ir.Port]).toVector
      val ports = (active.asInstanceOf[ir.Port] +: normalParamWires.map(_.asInstanceOf[ir.Port])) ++ normalRet.map(_.asInstanceOf[ir.Port])
      val stmts = activeOff ++ paramInvalids ++ retInit

      (Left(futurePorts ++ futureRetPort), ports, stmts.toVector, retFuture)
    } else {
      val future = args
        .map{ case (name, DataInstance(tpe, _)) => name -> tpe }
        .filter{ case (_, tpe) => tpe.symbol == Symbol.future }
        .map{ case (name, tpe) => ir.Reference(name.name, ir.UnknownType) -> tpe }
        .map{ case (refer, _) => Future(Map.empty, Map(refer -> FormKind.Field)) }
        .foldLeft(retFuture)(_ + _)

      val futureWires = futureParamWires.map(_.asInstanceOf[ir.DefWire])
      val futureRetWire = futureRet.map(_.asInstanceOf[ir.DefWire]).toVector
      val wires = (active.asInstanceOf[ir.DefWire] +: normalParamWires.map(_.asInstanceOf[ir.DefWire])) ++ normalRet.map(_.asInstanceOf[ir.DefWire])
      val stmts = activeOff ++ paramInvalids ++ retInit

      (Right(futureWires ++ futureRetWire), Vector.empty, wires ++ stmts, future)
    }
  }

  def runInterface(interface: MethodContainer)(implicit stack: StackFrame, ctx: FirrtlContext, global: GlobalData): (ir.Conditionally, Future) = {
    val (stmts, stmtFutures) = interface.code.map(runStmt(_)).unzip
    val RunResult(retFuture, retStmts, instance) = runExpr(interface.ret)
    val methodRetTpe = interface.label.symbol.tpe.asMethodType.returnType
    val connect =
      if(methodRetTpe == Type.unitTpe || methodRetTpe.origin == Symbol.future) None
      else {
        val DataInstance(_, refer) = instance
        val connectTarget = ir.Reference(interface.retName, ir.UnknownType)
        val connect = ir.Connect(ir.NoInfo, connectTarget, refer)

        Some(connect)
      }

    val access =
      if(methodRetTpe.origin != Symbol.future) Future.empty
      else {
        val DataInstance(_, source) = instance
        val loc = ir.Reference(interface.retName, ir.UnknownType)
        val access = Map[ir.Expression, Vector[ir.Expression]](loc -> Vector(source))

        Future(access, Map.empty)
      }

    val cond = ir.Conditionally(
      ir.NoInfo,
      ir.Reference(interface.activeName, ir.UnknownType),
      ir.Block(stmts.flatten ++ retStmts ++ connect),
      ir.EmptyStmt
    )

    (cond, stmtFutures.foldLeft(retFuture + access)(_ + _))
  }

  def buildFuture(future: Future): Vector[ir.Statement] = {
    def memberRef(expr: ir.Expression): ir.SubField = ir.SubField(expr, "_member", ir.UnknownType)
    def dataRef(expr: ir.Expression): ir.SubField = ir.SubField(expr, "_data", ir.UnknownType)

    def buildHasSource(name: ir.Expression, froms: Vector[ir.Expression]): Vector[ir.Connect] = {
      val locMember = memberRef(name)
      val locData = dataRef(name)
      val fromMembers = froms.map(from => ir.SubField(from, "_member", ir.UnknownType))
      val fromDatas = froms.map(from => ir.SubField(from, "_data", ir.UnknownType))

      val memberOr = fromMembers.foldLeft[ir.Expression](ir.UIntLiteral(0)){
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
      case (refer @ ir.Reference(name, _), FormKind.Local(froms, tpe)) =>
        val wire = ir.DefWire(ir.NoInfo, name, tpe)
        (Some(wire), buildHasSource(refer, froms))
      case (refer @ ir.Reference(name, _), FormKind.Constructor(tpe)) =>
        val wire = ir.DefWire(ir.NoInfo, name, tpe)
        (Some(wire), buildConstructor(refer))
      case (refer, _) =>
        val froms = future.accesses.getOrElse(refer, Vector.empty)
        (None, buildHasSource(refer, froms))
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
        val retPort =
          if(interface.ret.tpe == toBackendType(Type.unitTpe)) None
          else Some(ir.Port(ir.NoInfo, retName, ir.Input, toFirrtlType(interface.ret.tpe)))
        val paramPorts = interface.params.map {
          case (name, tpe) => ir.Port(ir.NoInfo, buildName(name), ir.Output, toFirrtlType(tpe))
        }.toVector

        val activeInit = ir.Connect(ir.NoInfo, ir.Reference(activeName, ir.UnknownType), ir.UIntLiteral(0))
        val (futureParams, normalParams) = interface.params.partition{ case (_, tpe) => tpe.symbol == Symbol.future }

        val paramInits = normalParams
          .map{ case (name, _) => buildName(name) }
          .map(name => ir.IsInvalid(ir.NoInfo, ir.Reference(name, ir.UnknownType)))
          .toVector

        val futureElems = futureParams
          .map{ case (name, _) => buildName(name) }
          .map(name => ir.Reference(name, ir.UnknownType) -> FormKind.Field)
          .toMap[ir.Expression, FormKind]

        val future = Future(Map.empty, futureElems)

        (future, (activePort +: paramPorts) ++ retPort, activeInit +: paramInits)
    }

    val (futures, ports, inits) = pairs.unzip3

    (futures.foldLeft(Future.empty)(_ + _), ports.flatten, inits.flatten)
  }

  def runStmt(stmt: backend.Stmt)(implicit stack: StackFrame, ctx: FirrtlContext, global: GlobalData): (Vector[ir.Statement], Future) = {
    def buildConnect(name: Name, expr: backend.Expr)(connect: DataInstance => Either[Future, Vector[ir.Statement]]): (Instance, Vector[ir.Statement], Future) = {
      val RunResult(exprFuture, stmts, instance) = runExpr(expr)

      val (inst, defStmts, stmtFuture) = instance match {
        case inst: ModuleInstance => (inst, Vector.empty, Future.empty)
        case inst: DataInstance => connect(inst) match {
          case Left(future) =>
            val wireInst = DataInstance(inst.tpe, ir.Reference(name.name, ir.UnknownType))
            (wireInst, Vector.empty, future)
          case Right(stmts) =>
            val wireInst = DataInstance(inst.tpe, ir.Reference(name.name, ir.UnknownType))
            (wireInst, stmts, Future.empty)
        }
      }

      (inst, stmts ++ defStmts, exprFuture + stmtFuture)
    }

    stmt match {
      case backend.Variable(name, tpe, expr) =>
        val varName = stack.next(name)

        val (inst, stmts, future) = buildConnect(varName, expr){
          case inst if inst.tpe.symbol == Symbol.future =>
            val firrtlType = toFirrtlType(tpe)
            val local = FormKind.Local(Vector(inst.refer), firrtlType)
            val refer = ir.Reference(varName.name, ir.UnknownType)
            val future = Map[ir.Expression, FormKind](refer -> local)

            Left(Future(Map.empty, future))

          case inst =>
            val expr = inst.refer
            val firrtlType = toFirrtlType(tpe)
            val varDef = ir.DefWire(ir.NoInfo, varName.name, firrtlType)
            val connect = ir.Connect(ir.NoInfo, ir.Reference(varName.name, ir.UnknownType), expr)

            Right(Vector(varDef, connect))
        }

        stack.append(varName, inst)
        (stmts, future)
      case backend.Temp(id, expr) =>
        val tempName = stack.next(id)

        val (inst, stmts, future) = buildConnect(tempName, expr) {
          case DataInstance(tpe, refer) if tpe.symbol == Symbol.future =>
            val firrtlType = toFirrtlType(tpe)
            val local = FormKind.Local(Vector(refer), firrtlType)
            val referTemp = ir.Reference(tempName.name, ir.UnknownType)
            val future = Map[ir.Expression, FormKind](referTemp -> local)

            Left(Future(Map.empty, future))
          case DataInstance(_, refer) =>
            val node = ir.DefNode(ir.NoInfo, tempName.name, refer)
            Right(Vector(node))
        }

        stack.append(tempName, inst)
        (stmts, future)
      case backend.Assign(target, expr) =>
        val targetName = stack.refer(target.name)
        val DataInstance(_, rightRefer) = stack.lookup(targetName)

        val RunResult(future, stmts, DataInstance(_, leftRefer)) = runExpr(expr)
        val connect = ir.Connect(ir.NoInfo, rightRefer, leftRefer)

        (stmts :+ connect, future)
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
      case construct: backend.ConstructEnum => runConstructEnum(construct)
      case call: backend.CallMethod => runCallMethod(call)
      case call: backend.CallInterface => runCallInterface(call)
      case call: backend.CallBuiltIn => runCallBuiltIn(call)
      case ifExpr: backend.IfExpr => runIfExpr(ifExpr)
      case matchExpr: backend.Match => runMatch(matchExpr)
      case finish: backend.Finish => runFinish(finish)
      case goto: backend.Goto => runGoto(goto)
      case generate: backend.Generate => runGenerate(generate)
      case ret: backend.Return => runReturn(ret)
      case backend.IntLiteral(value) => RunResult(Future.empty, Vector.empty, DataInstance(value))
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

    val method = call.accessor match {
      case Some(backend.Term.Temp(_, tpe)) => ctx.methods(tpe).find(_.label == call.label).get
      case Some(backend.Term.Variable(_, tpe)) => ctx.methods(tpe).find(_.label == call.label).get
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
    def callInternal(tpe: BackendType): RunResult = {
      val candidates = ctx.interfaces(tpe)
      val interface = candidates.find(_.label == call.label).get

      val normalParams = interface.params
        .filter { case (_, tpe) =>tpe.symbol != Symbol.future }
        .map{ case (name, _) => stack.refer(name) }
        .map{ name => ir.Reference(name.name, ir.UnknownType) }

      val futureParams = interface.params
        .filter{ case (_, tpe) => tpe.symbol == Symbol.future }
        .map { case (name, _) => stack.refer(name) }

      val argNames = call.args.map {
        case backend.Term.Temp(id, _) => stack.refer(id)
        case backend.Term.Variable(name, _) => stack.refer(name)
      }
      val argInstances = argNames.map(stack.lookup)

      val normalArgs = argInstances
        .map(_.asInstanceOf[DataInstance])
        .filter{ case DataInstance(tpe, _) => tpe.symbol != Symbol.future }
        .map(inst => inst.refer)

      val futureArgs= argInstances
        .map(_.asInstanceOf[DataInstance])
        .filter{ case DataInstance(tpe, _) => tpe.symbol == Symbol.future }
        .map(inst => inst.refer)

      val activate: ir.Statement = {
        val refer = ir.Reference(interface.activeName, ir.UnknownType)
        ir.Connect(ir.NoInfo, refer, ir.UIntLiteral(1))
      }
      val referReturn: Option[ir.Reference] = interface.ret match {
        case backend.UnitLiteral() => None
        case _ => Some(ir.Reference(interface.retName, ir.UnknownType))
      }

      val connects = (normalParams zip normalArgs).map{ case (param, arg) => ir.Connect(ir.NoInfo, param, arg) }.toVector

      val accesses = (futureParams zip futureArgs)
        .map{ case (param, arg) => ir.Reference(param.name, ir.UnknownType) -> arg }
        .map{ case (param, arg) => param -> Vector(arg) }
        .toMap[ir.Expression, Vector[ir.Expression]]

      val future = Future(accesses, Map.empty)

      val instance = referReturn match {
        case None => DataInstance()
        case Some(refer) => StructInstance(call.tpe, refer)
      }

      RunResult(future, activate +: connects, instance)
    }

    def callToSubModule(module: ir.Reference, tpe: BackendType): RunResult = {
      val candidates = ctx.interfaces(tpe)
      val interface = candidates.find(_.label == call.label).get
      val (futureParams, normalParams) = interface.params
        .toVector
        .map{ case (name, tpe) => ir.SubField(module, name, ir.UnknownType) -> tpe }
        .partition{ case (_, tpe) => tpe.symbol == Symbol.future }

      val argNames = call.args.map {
        case backend.Term.Temp(id, _) => stack.refer(id)
        case backend.Term.Variable(name, _) => stack.refer(name)
      }
      val (futureArgs, normalArgs) = argNames.map(stack.lookup)
        .map(_.asInstanceOf[DataInstance])
        .map{ case DataInstance(tpe, refer) => tpe -> refer }
        .partition{ case (tpe, _) => tpe.symbol == Symbol.future }

      val activate: ir.Statement = {
        val subField = ir.SubField(module, interface.activeName, ir.UnknownType)
        ir.Connect(ir.NoInfo, subField, ir.UIntLiteral(1))
      }

      val referReturn: Option[ir.SubField] = interface.ret match {
        case backend.UnitLiteral() => None
        case _ => Some(ir.SubField(module, interface.retName, ir.UnknownType))
      }

      val connects = normalParams
        .map(_._1)
        .zip(normalArgs.map(_._2))
        .map{ case (p, a) => ir.Connect(ir.NoInfo, p, a) }

      val accesses = futureParams
        .map(_._1)
        .zip(futureArgs.map(_._2))
        .map{ case (p, a) => p -> Vector(a) }
        .toMap[ir.Expression, Vector[ir.Expression]]

      val future = Future(accesses, Map.empty)

      val instance = referReturn match {
        case None => DataInstance()
        case Some(refer) => DataInstance(call.tpe, refer)
      }

      RunResult(future, activate +: connects, instance)
    }

    def callToUpperModule(module: String, tpe: BackendType): RunResult = {
      val candidates = ctx.interfaces(tpe)
      val interface = candidates.find(_.label == call.label).get
      val (futureParams, normalParams) = interface.params
        .toVector
        .map{ case (name, tpe) => ir.Reference(module + "$" + name, ir.UnknownType) -> tpe }
        .partition{ case (_, tpe) => tpe.symbol == Symbol.future }

      val argNames = call.args.map {
        case backend.Term.Temp(id, _) => stack.refer(id)
        case backend.Term.Variable(name, _) => stack.refer(name)
      }

      val (futureArgs, normalArgs) = argNames.map(stack.lookup)
        .map{ case DataInstance(tpe, refer) => tpe -> refer }
        .partition{ case (tpe, _) => tpe.symbol == Symbol.future }

      val activate: ir.Statement = {
        val activeRef = ir.Reference(module + "$" + interface.activeName, ir.UnknownType)
        ir.Connect(ir.NoInfo, activeRef, ir.UIntLiteral(1))
      }

      val referReturn = interface.ret match {
        case backend.UnitLiteral() => None
        case _ => Some(ir.Reference(module+ "$" + interface.retName, ir.UnknownType))
      }

      val connects = (normalParams.map(_._1) zip normalArgs.map(_._2)).map {
        case (p, a) => ir.Connect(ir.NoInfo, p, a)
      }

      val accesses = (futureParams.map(_._1) zip futureArgs.map(_._2))
        .map { case (p, a) => p -> Vector(a) }
        .toMap[ir.Expression, Vector[ir.Expression]]

      val future = Future(accesses, Map.empty)

      val instance = referReturn match {
        case None => DataInstance()
        case Some(refer) => DataInstance(call.tpe, refer)
      }

      RunResult(future, activate +: connects, instance)
    }

    val referName = call.accessor match {
      case backend.Term.Temp(id, _) => stack.refer(id)
      case backend.Term.Variable(name, _) => stack.refer(name)
    }

    stack.lookup(referName) match {
      case ModuleInstance(tpe, ModuleLocation.This) => callInternal(tpe)
      case ModuleInstance(tpe, ModuleLocation.Sub(refer)) => callToSubModule(refer, tpe)
      case ModuleInstance(tpe, ModuleLocation.Upper(refer)) => callToUpperModule(refer, tpe)
    }
  }

  def runCallBuiltIn(call: backend.CallBuiltIn)(implicit stack: StackFrame, ctx: FirrtlContext, global: GlobalData): RunResult = {
    def getInstance(term: backend.Term): Instance =
      term match {
        case backend.Term.Temp(id, _) => stack.lookup(stack.refer(id))
        case backend.Term.Variable(name, _) => stack.lookup(stack.refer(name))
      }

    val insts = call.args.map(getInstance)

    val instance = call.label match {
      case "_builtin_add_int" => builtin.intAdd(insts(0), insts(1), global)
      case "_builtin_sub_int" => builtin.intSub(insts(0), insts(1), global)
      case "_builtin_mul_int" => builtin.intMul(insts(0), insts(1), global)
      case "_builtin_div_int" => builtin.intDiv(insts(0), insts(1), global)
      case "_builtin_eq_int"  => builtin.intEq(insts(0), insts(1), global)
      case "_builtin_ne_int"  => builtin.intNe(insts(0), insts(1), global)
      case "_builtin_gt_int"  => builtin.intGt(insts(0), insts(1), global)
      case "_builtin_ge_int"  => builtin.intGe(insts(0), insts(1), global)
      case "_builtin_lt_int"  => builtin.intLt(insts(0), insts(1), global)
      case "_builtin_le_int"  => builtin.intLe(insts(0), insts(1), global)
      case "_builtin_neg_int" => builtin.intNeg(insts(0), global)
      case "_builtin_not_int" => builtin.intNot(insts(0), global)
      case "_builtin_eq_bool" => builtin.boolEq(insts(0), insts(1), global)
      case "_builtin_ne_bool" => builtin.boolNe(insts(0), insts(1), global)
      case "_builtin_not_bool"=> builtin.boolNot(insts(0), global)
      case "_builtin_add_bit" => builtin.bitAdd(insts(0), insts(1))
      case "_builtin_sub_bit" => builtin.bitSub(insts(0), insts(1))
      case "_builtin_mul_bit" => builtin.bitMul(insts(0), insts(1))
      case "_builtin_div_bit" => builtin.bitDiv(insts(0), insts(1))
      case "_builtin_eq_bit"  => builtin.bitEq(insts(0), insts(1))
      case "_builtin_ne_bit"  => builtin.bitNe(insts(0), insts(1))
      case "_builtin_gt_bit"  => builtin.bitGt(insts(0), insts(1))
      case "_builtin_ge_bit"  => builtin.bitGe(insts(0), insts(1))
      case "_builtin_lt_bit"  => builtin.bitLt(insts(0), insts(1))
      case "_builtin_le_bit"  => builtin.bitLe(insts(0), insts(1))
      case "_builtin_neg_bit" => builtin.bitNeg(insts(0))
      case "_builtin_not_bit" => builtin.bitNot(insts(0))
    }

    RunResult(Future.empty, Vector.empty, instance)
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

    def connectRet(wire: Option[ir.Reference], instance: Instance): Option[ir.Connect] =
      wire.flatMap { wire =>
        instance match {
          case DataInstance(tpe, refer) =>
            if(tpe.symbol == Symbol.future) None
            else Some(ir.Connect(ir.NoInfo, wire, refer))
          case _ => None
        }}

    def buildCondition(condRef: ir.Expression): RunResult = {
      lazy val retName = stack.next("_IFRET")

      val retWire =
        if(ifExpr.tpe.symbol == Symbol.unit || ifExpr.tpe.symbol == Symbol.future) None
        else Some(ir.DefWire(ir.NoInfo, retName.name, toFirrtlType(ifExpr.tpe)))

      val wireRef = retWire.map(wire => ir.Reference(wire.name, ir.UnknownType))

      val RunResult(conseqFuture, conseqStmts, conseqInst) = runInner(ifExpr.conseq, ifExpr.conseqLast)
      val RunResult(altFuture, altStmts, altInst) = runInner(ifExpr.alt, ifExpr.altLast)
      val conseqRet = connectRet(wireRef, conseqInst)
      val altRet = connectRet(wireRef, altInst)

      val whenStmt = ir.Conditionally (
        ir.NoInfo,
        condRef,
        ir.Block(conseqStmts ++ conseqRet),
        ir.Block(altStmts ++ altRet)
      )

      val retInstance = wireRef match {
        case None => DataInstance()
        case Some(wireRef) => StructInstance(ifExpr.tpe, wireRef)
      }

      val retFuture =
        if(ifExpr.tpe.symbol != Symbol.future) Map.empty[ir.Expression, FormKind]
        else {
          val referRet = ir.Reference(retName.name, ir.UnknownType)
          val refers = Vector(
            conseqInst.asInstanceOf[DataInstance].refer,
            altInst.asInstanceOf[DataInstance].refer,
          )

          Map[ir.Expression, FormKind](referRet -> FormKind.Local(refers, toFirrtlType(ifExpr.tpe)))
        }

      val future = conseqFuture + altFuture + Future(Map.empty, retFuture)
      RunResult(future, retWire.toVector :+ whenStmt, retInstance)
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
      }

    def uniqueVariantCases(cases: Vector[backend.Case]): Vector[backend.Case] = {
      cases.foldLeft(Vector.empty[backend.Case]) {
        case (stacked, caseElem) =>
          val hasSameVariant = stacked.exists(_.cond.variant == caseElem.cond.variant)

          if(hasSameVariant) stacked
          else stacked :+ caseElem
      }
    }

    def extractForEachVariant(source: ir.SubField, cond: backend.CaseCond): (Vector[ir.Statement], Vector[Name]) = {
      val terms = cond.variables
      val tpes = terms.map(_.tpe).map(toFirrtlType)

      val (stmts, names, _) = tpes.foldLeft(Vector.empty[ir.Statement], Vector.empty[Name], BigInt(0)) {
        case ((stmts, names, idx), tpe) =>
          val locName = stack.next("_EXTRACT")

          val (leafStmts, name, nextIdx) = extractFieldData(source, tpe, idx)
          val connect = ir.DefNode(ir.NoInfo, locName.name, ir.Reference(name.name, ir.UnknownType))

          (stmts ++ leafStmts :+ connect, names :+ locName, nextIdx)
      }

      (stmts, names)
    }

    def constructCase(
      caseStmt: backend.Case,
      member: ir.SubField,
      variants: Vector[Symbol.EnumMemberSymbol],
      table: Map[Symbol.EnumMemberSymbol, Vector[Name]],
      retWire: Option[String]
    ): (Vector[ir.Statement], ir.Block, Name, Future) = {
      val patternIdx = variants.zipWithIndex
        .find { case (variant, _) => caseStmt.cond.variant == variant }
        .map { case (_, idx) => idx }
        .map(ir.UIntLiteral(_))
        .get

      val sources = table(caseStmt.cond.variant)
      val sinks = caseStmt.cond.variables.map {
        case backend.Term.Variable(name, _) => stack.next(name)
        case backend.Term.Temp(id, _) => stack.next(id)
      }

      caseStmt.cond.variables.map {
        case backend.Term.Variable(name, tpe) => stack.refer(name) -> tpe
        case backend.Term.Temp(id, tpe) => stack.refer(id) -> tpe
      }.foreach {
        case (sink, tpe) =>
          val instance = DataInstance(tpe, ir.Reference(sink.name, ir.UnknownType))
          stack.append(sink, instance)
      }

      val nodes = (sinks zip sources).map{
        case (sink, source) =>
          ir.DefNode(
            ir.NoInfo,
            sink.name,
            ir.Reference(source.name, ir.UnknownType)
          )
      }

      val (caseCondFutures, caseCondStmtss, caseCondExpr) = caseStmt.cond.conds
        .map {
          case (backend.Term.Variable(name, _), expr) => stack.refer(name).name -> expr
          case (backend.Term.Temp(id, _), expr) => stack.refer(id).name -> expr
        }
        .map {
          case (source, expr) =>
            val RunResult(future, stmts, DataInstance(_, refer)) = runExpr(expr)
            val eqn = ir.DoPrim(
              PrimOps.Eq,
              Seq(ir.Reference(source, ir.UnknownType), refer),
              Seq.empty,
              ir.UnknownType
            )

            (future, stmts, eqn)
        }
        .unzip3

      val caseName = stack.next("_MATCH")
      val patternCond = ir.DoPrim(PrimOps.Eq, Seq(member, patternIdx), Seq.empty, ir.UnknownType)
      val condNode = caseCondExpr
        .reduceLeftOption[ir.Expression]{ case (conds, cond) => ir.DoPrim(PrimOps.And, Seq(conds, cond), Seq.empty, ir.UnknownType) }
        .map { cond => ir.DoPrim(PrimOps.And, Seq(cond, patternCond), Seq.empty, ir.UnknownType)}
        .map { cond => ir.DefNode(ir.NoInfo, caseName.name, cond) }
        .getOrElse(ir.DefNode(ir.NoInfo, caseName.name, patternCond))

      val condStmts = nodes ++ caseCondStmtss.flatten :+ condNode

      val (bodyStmtss, bodyFutures) = caseStmt.stmts.map(runStmt).unzip
      val RunResult(retFuture, retStmts, instance) = runExpr(caseStmt.ret)

      val retConnect = retWire
        .map(name => ir.Reference(name, ir.UnknownType))
        .map(loc => ir.Connect(ir.NoInfo, loc, instance.asInstanceOf[DataInstance].refer))

      val caseBody = ir.Block(bodyStmtss.flatten ++ retStmts ++ retConnect)

      val future = (bodyFutures ++ caseCondFutures).foldLeft(retFuture)(_ + _)
      (condStmts, caseBody, caseName, future)
    }

    def run(instance: DataInstance, cases: Vector[backend.Case], retTpe: BackendType): RunResult = {
      val enum = instance.tpe.symbol.asEnumSymbol
      val dataRef = ir.SubField(instance.refer, "_data", ir.UnknownType)
      val allVariants = enum.tpe.declares
        .toMap.values.toVector
        .sortWith{ case (left, right) => left.name < right.name }
        .map(_.asEnumMemberSymbol)

      val conds = uniqueVariantCases(cases).map(_.cond)
      val (variants, pairs) = conds.map(cond => cond.variant -> extractForEachVariant(dataRef, cond)).unzip
      val (stmtss, namess) = pairs.unzip
      val fieldSourceTable = (variants zip namess).toMap

      val retWireInfo =
        if(retTpe == toBackendType(Type.unitTpe)) None
        else Some(stack.next("_MATCH_RET"), toFirrtlType(retTpe))

      val retWire = retWireInfo.map{ case (name, tpe) => ir.DefWire(ir.NoInfo, name.name, tpe) }

      val memberRef = ir.SubField(instance.refer, "_member", ir.UnknownType)
      val (caseStmtss, caseBodies, caseNames, caseFutures) = cases
        .map(constructCase(_, memberRef, allVariants, fieldSourceTable, retWire.map(_.name)))
        .unzip4

      val stopStmt = ir.Stop(ir.NoInfo, 1, clockRef, ir.UIntLiteral(1))
      val caseConds = (caseNames zip caseBodies).foldRight[ir.Statement](stopStmt) {
        case ((name, conseq), alt) =>
          val refer = ir.Reference(name.name, ir.UnknownType)
          ir.Conditionally(ir.NoInfo, refer, conseq, alt)
      }

      val retInvalid = retWire.map(wire => ir.IsInvalid(ir.NoInfo, ir.Reference(wire.name, ir.UnknownType)))
      val matchStmts = Vector(retWire, retInvalid).flatten ++ stmtss.flatten ++ caseStmtss.flatten :+ caseConds
      val retInstance = retWire
        .map(wire => DataInstance(retTpe, ir.Reference(wire.name, ir.UnknownType)))
        .getOrElse(DataInstance())

      val future = caseFutures.foldLeft(Future.empty)(_ + _)
      RunResult(future, matchStmts, retInstance)
    }

    /*
    def runSoftMatch(instance: SoftInstance, cases: Vector[backend.Case]): RunResult = {
      def runCaseBody(caseStmt: backend.Case): RunResult = {
        val (stmtss, futures) = caseStmt.stmts.map(runStmt).unzip
        val RunResult(retFuture, retStmts, retInstance) = runExpr(caseStmt.ret)

        val future = futures.foldLeft(retFuture)(_ + _)
        RunResult(future, stmtss.flatten ++ retStmts, retInstance)
      }

      def verifyCondition(caseStmt: backend.Case, cond: backend.CaseCond, enum: EnumSoftInstance): Option[RunResult] = {
        val instances = enum.field.values.toVector
        val names = cond.variables.map {
          case backend.Term.Variable(name, _) => stack.next(name)
          case backend.Term.Temp(id, _) => stack.next(id)
        }

        (names zip instances).foreach { case (name, inst) => stack.append(name, inst) }

        val condPairs = cond.conds.map {
          case (backend.Term.Variable(name, _), expr) => stack.lookup(stack.refer(name)) -> expr
          case (backend.Term.Temp(id, _), expr) => stack.lookup(stack.refer(id)) -> expr
        }

        val (condStmts, condFuture, condResult) = condPairs
          .map{ case (inst, expr) => inst -> runExpr(expr) }
          .foldLeft(Vector.empty[ir.Statement], Future.empty, true){
            case ((stmts, future, false), _) => (stmts, future, false)
            case ((stmts, future, true), (inst, RunResult(runFuture, runStmts, runInst))) =>
              val cond = (inst, runInst) match {
                case (IntInstance(left), IntInstance(right)) => left == right
                case (UnitInstance(), UnitInstance()) => true
                case (StringInstance(left), StringInstance(right)) => left == right
                case _ => throw new ImplementationErrorException("other pattern must be rejected by compile error in front end")
              }

              (stmts ++ runStmts, future + runFuture, cond)
          }

        if(!condResult) None
        else {
          val RunResult(bodyFuture, bodyStmts, instance) = runCaseBody(caseStmt)
          Some(RunResult(bodyFuture + condFuture, condStmts ++ bodyStmts, instance))
        }
      }

      def matchPattern(caseStmt: backend.Case, enum: EnumSoftInstance): Option[RunResult] =
        if(caseStmt.cond.variant != enum.variant) None
        else verifyCondition(caseStmt, caseStmt.cond, enum)

      instance match {
        case enum: EnumSoftInstance =>
          cases.foldLeft(Option.empty[RunResult]) {
            case (Some(result), _) => Some(result)
            case (None, caseStmt) => matchPattern(caseStmt, enum)
          }.get
        case _ => throw new ImplementationErrorException("pattern match except for enum is not supported yet")
      }
    }
    */

    val backend.Match(matched, cases, tpe) = matchExpr
    val instance = stack.lookup(stack.refer(matched.id))

    run(instance.asInstanceOf[DataInstance], cases, tpe)
  }

  def runConstructStruct(construct: backend.ConstructStruct)(implicit stack: StackFrame, ctx: FirrtlContext, global: GlobalData): RunResult = {
    def constructData(preStmts: Vector[ir.Statement], results: Map[String, RunResult]): RunResult = {
      val bundleType = toFirrtlType(construct.tpe)
      val bundleName = stack.next("_BUNDLE")
      val bundleRef = ir.Reference(bundleName.name, bundleType)
      val varDef = ir.DefWire(ir.NoInfo, bundleName.name, bundleType)
      val connects = results.mapValues(_.instance).map {
        case (name, DataInstance(_, expr)) =>
          val field = ir.SubField(bundleRef, name, expr.tpe)
          ir.Connect(ir.NoInfo, field, expr)
      }

      val stmts = varDef +: connects.toVector
      val refer = ir.Reference(bundleName.name, bundleType)
      val instance = StructInstance(construct.tpe, refer)

      RunResult(Future.empty, preStmts ++ stmts, instance)
    }

    /*
    def constructSoft(preStmts: Vector[ir.Statement], results: Map[String, RunResult]): RunResult = {
      val fieldElems = results.mapValues(_.instance)
      val instance = UserSoftInstance(construct.tpe, fieldElems)

      RunResult(Future.empty, preStmts, instance)
    }
    */

    val results = construct.pairs.map { case (key, value) => key -> runExpr(value) }
    val stmts = results.values.foldLeft(Vector.empty[ir.Statement]) {
      case (stmts, result) => stmts ++ result.stmts
    }

    constructData(stmts, results)
  }

  def runConstructModule(construct: backend.ConstructModule)(implicit stack: StackFrame, ctx: FirrtlContext, global: GlobalData): RunResult = {
    val moduleName = construct.name match {
      case backend.Term.Variable(name, _) => Name(name)
      case backend.Term.Temp(id, _) => stack.next(id)
    }

    val moduleRef = ir.Reference(moduleName.name, ir.UnknownType)

    def buildIndirectAccessCond(interface: MethodContainer, fromName: String)(targetBuilder: String => ir.Expression): (Future, Option[ir.IsInvalid], ir.Conditionally) = {
      val isUnitRet = interface.ret.tpe.symbol == Symbol.unit
      val isFutureRet = interface.ret.tpe.symbol == Symbol.future
      val targetActive = targetBuilder(interface.activeName)

      val targetRet =
        if(isUnitRet || isFutureRet) None
        else Some(targetBuilder(interface.retName))

      val (targetFutureParams, targetNormalParams) = interface.params
        .map{ case (param, tpe) => targetBuilder(param) -> tpe }
        .toVector
        .partition{ case (_, tpe) => tpe.symbol == Symbol.future }

      val normalTargets = targetActive +: targetNormalParams.map(_._1)

      def fromRef(name: String): ir.SubField = ir.SubField(moduleRef, fromName + "$" + name, ir.UnknownType)
      val fromActive = fromRef(interface.activeName)

      val fromRet =
        if(isUnitRet || isFutureRet) None
        else Some(fromRef(interface.retName))

      val retInvalid = fromRet.map(ret => ir.IsInvalid(ir.NoInfo, ret))
      val futureRet =
        if(!isFutureRet) Map.empty[ir.Expression, FormKind]
        else Map[ir.Expression, FormKind](fromRef(interface.retName) -> FormKind.Field)

      val (futureFromArgs, normalFromArgs) = interface.params.toVector
        .map { case (param, tpe) => fromRef(param) -> tpe }
        .partition{ case (_, tpe) => tpe.symbol == Symbol.future }

      val normalFroms = fromActive +: normalFromArgs.map(_._1)

      val connects = (normalTargets zip normalFroms).map { case (target, from) => ir.Connect(ir.NoInfo, target, from) }
      val retConnect = (fromRet zip targetRet).map{ case (from, target) => ir.Connect(ir.NoInfo, from, target) }

      val retAccess =
        if(!isFutureRet) Map.empty
        else Map[ir.Expression, Vector[ir.Expression]](fromRef(interface.retName) -> Vector(targetBuilder(interface.retName)))

      val futureTargets = targetFutureParams.map(_._1)
      val futureElems = futureTargets.map(_ -> FormKind.Field).toMap[ir.Expression, FormKind]
      val accesses = (futureTargets zip futureFromArgs.map(_._1)).map{ case (target, from) => target -> Vector(from) }.toMap ++ retAccess
      val future = Future(accesses, futureRet ++ futureElems)

      val cond = ir.Conditionally(
        ir.NoInfo,
        fromActive,
        ir.Block(connects ++ retConnect),
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
          val (futureParams, normalParams) = interface.params
            .toVector
            .map{ case (name, tpe) => buildRef(name) -> tpe }
            .partition{ case (_, tpe) => tpe.symbol == Symbol.future }

          val activeOff = ir.Connect(ir.NoInfo, activeRef, ir.UIntLiteral(0))
          val paramInvalid = normalParams
            .map(_._1)
            .map(ir.IsInvalid(ir.NoInfo, _))

          val futureElems = futureParams
              .map(_._1)
              .map(_ -> FormKind.Field)
              .toMap[ir.Expression, FormKind]

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

    val instance = ModuleInstance(construct.tpe, ModuleLocation.Sub(ir.Reference(moduleName.name, ir.UnknownType)))
    RunResult(future, stmts, instance)
  }

  def runConstructEnum(enum: backend.ConstructEnum)(implicit stack: StackFrame, ctx: FirrtlContext, global: GlobalData): RunResult = {
    def constructEnum: RunResult = {
      def splitValue(tpe: ir.Type, refer: ir.Expression): Vector[ir.Expression] = {
        tpe match {
          case ir.UIntType(_) => Vector(refer)
          case ir.BundleType(fields) =>
            val refers = fields.flatMap {
              field =>
                val underRefer = ir.SubField(refer, field.name, field.tpe)
                splitValue(field.tpe, underRefer)
            }

            refers.toVector
        }
      }

      val tpe = toFirrtlType(enum.target)
      val insts = enum.passed.map(temp => stack.lookup(stack.refer(temp.id)))

      val value = insts
        .map(_.asInstanceOf[DataInstance])
        .flatMap(inst => splitValue(toFirrtlType(inst.tpe), inst.refer))
        .reduceLeftOption[ir.Expression]{ case (prefix, refer) => ir.DoPrim(PrimOps.Cat, Seq(refer, prefix), Seq.empty, ir.UnknownType) }
        .getOrElse(ir.UIntLiteral(0))

      val flagValue = enum.tpe.symbol.tpe.declares
        .toMap.toVector
        .sortWith{ case ((left, _), (right, _)) => left < right }
        .map{ case (_, symbol) => symbol }
        .zipWithIndex
        .find{ case (symbol, _) => symbol ==  enum.variant }
        .map{ case (_, idx) => ir.UIntLiteral(idx) }
        .getOrElse(throw new ImplementationErrorException(s"${enum.variant} was not found"))

      val enumName = stack.next("_ENUM")
      val enumRef = ir.Reference(enumName.name, ir.UnknownType)
      val wireDef =
        if(enum.target.symbol == Symbol.future) None
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
        if(enum.target.symbol != Symbol.future) Future(Map.empty, Map.empty)
        else Future(Map.empty, Map(enumRef -> FormKind.Constructor(tpe)))

      RunResult(future, runResultStmts, instance)
    }

    /*
    def constructSoftEnum: RunResult = {
      val insts = enum.passed.map(temp => stack.lookup(stack.refer(temp.id)))
      val pairs = insts.zipWithIndex.map { case (inst, idx) => s"_$idx" -> inst }
      val table = ListMap.from(pairs)

      val instance = EnumSoftInstance(enum.target, enum.variant, table)

      RunResult(Future.empty, Vector.empty, instance)
    }
    */

    constructEnum
  }

  def runFinish(finish: backend.Finish)(implicit stack: StackFrame, ctx: FirrtlContext, global: GlobalData): RunResult = {
    val stageName = finish.stage.toString
    val active = stageName + "$_active"
    val activeRef = ir.Reference(active, ir.UnknownType)
    val finishStmt = ir.Connect(ir.NoInfo, activeRef, ir.UIntLiteral(0))

    RunResult(Future.empty, Vector(finishStmt), DataInstance())
  }

  def runGoto(goto: backend.Goto)(implicit stack: StackFrame, ctx: FirrtlContext, global: GlobalData): RunResult = {
    val stateIndex = goto.state.index
    val stageState = goto.state.stage.toString + "$_state"
    val stateRef = ir.Reference(stageState, ir.UnknownType)
    val changeState = ir.Connect(ir.NoInfo, stateRef, ir.UIntLiteral(stateIndex))

    RunResult(Future.empty, Vector(changeState), DataInstance())
  }

  def runGenerate(generate: backend.Generate)(implicit stack: StackFrame, ctx: FirrtlContext, global: GlobalData): RunResult = {
    val activeName = generate.stage.toString + "$_active"
    val activeRef = ir.Reference(activeName, ir.UnknownType)

    val normalArgNames = generate.args
      .filter(_.tpe.symbol != Symbol.future)
      .map {
        case backend.Term.Temp(id, _) => stack.refer(id)
        case backend.Term.Variable(name, _) => stack.refer(name)
      }

    val futureArgNames = generate.args
      .filter(_.tpe.symbol == Symbol.future)
      .map {
        case backend.Term.Temp(id, _) => stack.refer(id)
        case backend.Term.Variable(name, _) => stack.refer(name)
      }

    val normalArgRefs = normalArgNames.map(name => ir.Reference(name.name, ir.UnknownType))
    val futureArgRefs = futureArgNames.map(name => ir.Reference(name.name, ir.UnknownType))

    val stageContainer = ctx.stages(stack.lookupThis.get.tpe).find(_.label == generate.stage).get
    val normalParamNames = stageContainer.params.collect{ case (name, tpe) if tpe.symbol != Symbol.future => name }
    val futureParamNames = stageContainer.params.collect{ case (name, tpe) if tpe.symbol == Symbol.future => name }

    val normalParamRefs = normalParamNames.map(name => ir.Reference(name, ir.UnknownType))

    val activate = ir.Connect(ir.NoInfo, activeRef, ir.UIntLiteral(1))

    val normalParams = (normalParamRefs zip normalArgRefs).map{ case (param, arg) => ir.Connect(ir.NoInfo, param, arg) }
    val futureParams = (futureParamNames zip futureArgRefs)
      .map{ case (param, arg) => ir.Reference(param, ir.UnknownType) -> arg}
      .map{ case (param, arg) => param -> Vector(arg) }
      .toMap[ir.Expression, Vector[ir.Expression]]

    val future = Future(futureParams, Map.empty)

    val retInstance =
      if(stageContainer.ret.symbol == Symbol.unit) DataInstance()
      else DataInstance(stageContainer.ret, ir.Reference(stageContainer.retName, ir.UnknownType))

    RunResult(future, activate +: normalParams.toVector, retInstance)
  }

  def runReturn(ret: backend.Return)(implicit stack: StackFrame, ctx: FirrtlContext, global: GlobalData): RunResult = {
    val RunResult(exprFuture, stmts, instance) = runExpr(ret.expr)
    val loc = ir.Reference(ret.stage.retName, ir.UnknownType)
    val DataInstance(_, refer) = instance
    val retFuture = Future(Map(loc -> Vector(refer)), Map.empty)

    RunResult(exprFuture + retFuture, stmts, DataInstance())
  }

  def toFirrtlType(tpe: BackendType)(implicit global: GlobalData): ir.Type = {
    def toBitType(width: Int): ir.UIntType = ir.UIntType(ir.IntWidth(width))
    def toEnumType(symbol: Symbol.EnumSymbol): ir.BundleType = {
      def log2(x: Double): Double = math.log10(x) / math.log10(2.0)
      def flagWidth(x: Double): Double = (math.ceil _ compose log2)(x)

      def makeBitLength(
        member: Type.EnumMemberType,
        hpTable: Map[Symbol.HardwareParamSymbol, HPElem],
        tpTable: Map[Symbol.TypeParamSymbol, BackendType]
      ): BigInt = {
        def loop(tpe: ir.Type): BigInt = tpe match {
          case ir.BundleType(fields) => fields.map(_.tpe).map(loop).sum
          case ir.UIntType(ir.IntWidth(width)) => width
        }

        val fieldTypes = member.fields
          .map(_.tpe.asRefType)
          .map(toBackendType(_, hpTable, tpTable))
          .map(toFirrtlType)

        fieldTypes.map(loop).sum
      }

      val members = symbol.tpe.declares
        .toMap
        .toVector
        .sortWith{ case ((left, _), (right, _)) => left < right }
        .map{ case (_, symbol) => symbol }

      val kind =
        if(members.length <= 1) None
        else Some(ir.Field(
          "_member",
          ir.Default,
          ir.UIntType(ir.IntWidth(flagWidth(members.length).toInt))
        ))

      val hpTable = (symbol.hps zip tpe.hargs).toMap
      val tpTable = (symbol.tps zip tpe.targs).toMap

      val maxLength = members
        .map(_.tpe.asEnumMemberType)
        .map(makeBitLength(_, hpTable, tpTable))
        .max

      val dataStorage = Some(ir.Field("_data", ir.Default, ir.UIntType(ir.IntWidth(maxLength))))

      val field = Seq(kind, dataStorage).flatten
      ir.BundleType(field)
    }

    def toOtherType: ir.BundleType = {
      val typeFields = global.lookupFields(tpe)

      val fields = typeFields.map{ case (name, tpe) => name -> toFirrtlType(tpe) }
        .toVector
        .sortWith{ case ((left, _), (right, _)) => left < right }
        .map{ case (name, tpe) => ir.Field(name, ir.Default, tpe) }

      ir.BundleType(fields)
    }

    tpe.symbol match {
      case symbol if symbol == Symbol.int  => toBitType(width = 32)
      case symbol if symbol == Symbol.bool => toBitType(width = 1)
      case symbol if symbol == Symbol.unit => toBitType(width = 0)
      case symbol if symbol == Symbol.bit =>
        val HPElem.Num(width) = tpe.hargs.head
        toBitType(width)
      case symbol: Symbol.EnumSymbol => toEnumType(symbol)
      case _ => toOtherType
    }
  }
}
