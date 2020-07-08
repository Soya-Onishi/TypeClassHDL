package tchdl.backend

import tchdl.backend.{ast => backend}
import tchdl.util._
import tchdl.util.TchdlException._
import firrtl.{PrimOps, ir}

import scala.annotation.tailrec
import scala.collection.immutable.ListMap
import scala.collection.mutable
import scala.math


object FirrtlCodeGen {
  val clockName = "_CLK"
  val resetName = "_RESET"
  val clockRef = ir.Reference(clockName, ir.ClockType)
  val resetRef = ir.Reference(resetName, ir.UIntType(ir.IntWidth(1)))

  trait Instance {
    val tpe: BackendType

    def isHardware: Boolean
  }

  abstract class SoftInstance extends Instance {
    val tpe: BackendType
    val field: Map[String, Instance]

    override def isHardware = false
  }

  abstract class HardInstance extends Instance {
    val tpe: BackendType
    val reference: ir.Expression

    override def isHardware = true
  }

  abstract class ModuleInstance extends Instance {
    val tpe: BackendType
    val refer: ModuleLocation
  }

  trait ModuleLocation
  object ModuleLocation {
    case class Sub(refer: ir.Reference) extends ModuleLocation
    case class Upper(refer: String) extends ModuleLocation
    case object This extends ModuleLocation
  }


  object SoftInstance {
    def unapply(obj: Any): Option[(BackendType, Map[String, Instance])] =
      obj match {
        case instance: SoftInstance => Some(instance.tpe, instance.field)
        case _ => None
      }
  }

  object HardInstance {
    def apply(tpe: BackendType, refer: ir.Expression)(implicit global: GlobalData): HardInstance =
      tpe.symbol match {
        case symbol if symbol == global.builtin.types.lookup("Bit") => BitInstance(tpe, refer)
        case _ => UserHardInstance(tpe, refer)
      }

    def unapply(obj: Any): Option[(BackendType, ir.Expression)] =
      obj match {
        case instance: HardInstance => Some(instance.tpe, instance.reference)
        case _ => None
      }
  }

  object ModuleInstance {
    def apply(module: BackendType, refer: ModuleLocation): ModuleInstance = {
      val _refer = refer

      new ModuleInstance {
        val refer = _refer
        val tpe = module

        override def isHardware: Boolean = false
      }
    }

    def unapply(obj: Any): Option[(BackendType, ModuleLocation)] =
      obj match {
        case inst: ModuleInstance => Some(inst.tpe, inst.refer)
        case _ => None
      }
  }

  case class UserSoftInstance(tpe: BackendType, field: Map[String, Instance]) extends SoftInstance
  case class EnumSoftInstance(tpe: BackendType, variant: Symbol.EnumMemberSymbol, field: ListMap[String, Instance]) extends SoftInstance
  case class IntInstance(value: Int)(implicit global: GlobalData) extends SoftInstance {
    val field = Map.empty
    val tpe = toBackendType(Type.intTpe, Map.empty, Map.empty)
  }

  case class StringInstance(value: String)(implicit global: GlobalData) extends SoftInstance {
    val field = Map.empty
    val tpe = toBackendType(Type.stringTpe, Map.empty, Map.empty)
  }

  case class BoolInstance(value: Boolean)(implicit global: GlobalData) extends SoftInstance {
    val field = Map.empty
    val tpe = toBackendType(Type.boolTpe, Map.empty, Map.empty)
  }

  case class UnitInstance()(implicit global: GlobalData) extends SoftInstance {
    val field = Map.empty
    val tpe = toBackendType(Type.unitTpe, Map.empty, Map.empty)
  }

  case class UserHardInstance(tpe: BackendType, reference: ir.Expression) extends HardInstance
  case class BitInstance(tpe: BackendType, reference: ir.Expression) extends HardInstance

  case class FirrtlContext(
    interfaces: Map[BackendType, Vector[MethodContainer]],
    stages: Map[BackendType, Vector[StageContainer]],
    methods: Map[BackendType, Vector[MethodContainer]],
  )

  abstract class StackFrame {
    protected def parent: StackFrame

    val scope: mutable.Map[Name, Instance] = mutable.Map.empty
    val namer: FirrtlNamer
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

    def assert(name: Name, instance: Instance): Unit = {
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

  case class Name(name: String) {
    override def hashCode(): Int = name.hashCode
  }

  case class RunResult(stmts: Vector[ir.Statement], instance: Instance)

  def exec(topModule: BackendType, modules: Vector[ModuleContainer], methods: Vector[MethodContainer])(implicit global: GlobalData): ir.Circuit = {
    val interfaceTable = modules.map(module => module.tpe -> module.interfaces).toMap
    val stageTable = modules.map(module => module.tpe -> module.stages).toMap
    val methodTable = methods.groupBy(_.label.accessor)

    val firrtlModules = modules.map(buildModule(_, interfaceTable, stageTable, methodTable))
    val circuitName = topModule.toFirrtlString

    ir.Circuit(ir.NoInfo, firrtlModules, circuitName)
  }

  def buildModule(
    module: ModuleContainer,
    interfaces: Map[BackendType, Vector[MethodContainer]],
    stages: Map[BackendType, Vector[StageContainer]],
    methods: Map[BackendType, Vector[MethodContainer]]
  )(implicit global: GlobalData): ir.Module = {
    val instance = ModuleInstance(module.tpe, ModuleLocation.This)

    val ctx = FirrtlContext(interfaces, stages, methods)
    val stack = StackFrame(instance)

    module.hps
      .map { case (name, elem) => stack.next(name) -> elem }
      .foreach {
        case (name, HPElem.Num(num)) => stack.scope(name) = IntInstance(num)
        case (name, HPElem.Str(str)) => stack.scope(name) = StringInstance(str)
      }

    val (inputStmts, inputs) = module.fields
      .filter(_.flag.hasFlag(Modifier.Input))
      .map(runInput(_)(stack, ctx, global))
      .unzip

    val (outputStmts, outputs) = module.fields
      .filter(_.flag.hasFlag(Modifier.Output))
      .map(runOutput(_)(stack, ctx, global))
      .unzip

    val (internalStmts, internals) = module.fields
      .filter(_.flag.hasFlag(Modifier.Internal))
      .map(runInternal(_)(stack, ctx, global))
      .unzip

    val (regStmts, registers) = module.fields
      .filter(_.flag.hasFlag(Modifier.Register))
      .map(runRegister(_)(stack, ctx, global))
      .unzip

    val (moduleStmts, modules) = module.fields
      .filter(_.flag.hasFlag(Modifier.Child))
      .map(runSubModule(_)(stack, ctx, global))
      .unzip

    val clk = ir.Port(ir.NoInfo, clockName, ir.Input, ir.ClockType)
    val reset = ir.Port(ir.NoInfo, resetName, ir.Input, ir.UIntType(ir.IntWidth(1)))
    val ports = Vector(clk, reset) ++ inputs ++ outputs
    val initStmts = (inputStmts ++ outputStmts ++ internalStmts ++ regStmts ++ moduleStmts).flatten
    val components = internals ++ registers ++ modules
    val fieldStmts = components ++ initStmts

    val alwaysStmts = module.always.flatMap(runAlways(_)(stack, ctx, global))
    val (interfacePorts, interfaceStmts) = module.interfaces.map(buildInterfaceSignature(_)(stack, global)).unzip
    val interfaceConds = module.interfaces.map(runInterface(_)(stack, ctx, global))
    val stageStmts = module.stages.flatMap(buildStageSignature(_)(stack, global))
    val stageConds = module.stages.map(runStage(_)(stack, ctx, global))
    val moduleField = global.lookupFields(module.tpe)
    val (upperPorts, upperPortInits) = moduleField.map{ case (name, tpe) => buildUpperModule(name, tpe)(ctx, global) }.toVector.unzip

    ir.Module(
      ir.NoInfo,
      module.tpe.toFirrtlString,
      ports ++ interfacePorts.flatten ++ upperPorts.flatten,
      ir.Block(interfaceStmts.flatten ++ upperPortInits.flatten ++ fieldStmts ++ stageStmts ++ alwaysStmts ++ interfaceConds ++ stageConds)
    )
  }

  def runInput(field: FieldContainer)(implicit stack: StackFrame, ctx: FirrtlContext, global: GlobalData): (Vector[ir.Statement], ir.Port) = {
    val stmts = field.code.flatMap(runStmt)
    val retExpr = field.ret.map(throw new ImplementationErrorException("input wire with init expression is not supported yet"))
    val firrtlType = toFirrtlType(field.tpe)

    val port = ir.Port(ir.NoInfo, field.toFirrtlString, ir.Input, firrtlType)

    (stmts, port)
  }

  def runOutput(field: FieldContainer)(implicit stack: StackFrame, ctx: FirrtlContext, global: GlobalData): (Vector[ir.Statement], ir.Port) = {
    val stmts = field.code.flatMap(runStmt)
    val fieldRef = ir.Reference(field.toFirrtlString, ir.UnknownType)
    val retStmt = field.ret
      .map(runExpr)
      .map{ case RunResult(stmts, HardInstance(_, refer)) => (stmts, refer) }
      .map{ case (stmts, refer) => stmts :+ ir.Connect(ir.NoInfo, fieldRef, refer) }
      .getOrElse(Vector(ir.IsInvalid(ir.NoInfo, fieldRef)))
    val tpe = toFirrtlType(field.tpe)
    val port = ir.Port(ir.NoInfo, field.toFirrtlString, ir.Output, tpe)

    (stmts ++ retStmt, port)
  }

  def runInternal(field: FieldContainer)(implicit stack: StackFrame, ctx: FirrtlContext, global: GlobalData): (Vector[ir.Statement], ir.DefWire) = {
    val stmts = field.code.flatMap(runStmt)
    val fieldRef = ir.Reference(field.toFirrtlString, ir.UnknownType)
    val retStmt = field.ret
      .map(runExpr)
      .map{ case RunResult(stmts, HardInstance(_, refer)) => (stmts, refer) }
      .map{ case (stmts, refer) => stmts :+ ir.Connect(ir.NoInfo, fieldRef, refer) }
      .getOrElse(Vector(ir.IsInvalid(ir.NoInfo, fieldRef)))
    val tpe = toFirrtlType(field.tpe)
    val wire = ir.DefWire(ir.NoInfo, field.toFirrtlString, tpe)

    (stmts ++ retStmt, wire)
  }

  def runRegister(field: FieldContainer)(implicit stack: StackFrame, ctx: FirrtlContext, global: GlobalData): (Vector[ir.Statement], ir.DefRegister) = {
    val stmts = field.code.flatMap(runStmt)
    val fieldRef = ir.Reference(field.toFirrtlString, ir.UnknownType)
    val (retStmts, retExpr) = field.ret
      .map(runExpr)
      .map{ case RunResult(stmts, HardInstance(_, refer)) => (stmts, refer) }
      .getOrElse((Vector.empty, fieldRef))
    val tpe = toFirrtlType(field.tpe)
    val reg = ir.DefRegister(ir.NoInfo, field.toFirrtlString, tpe, clockRef, resetRef, retExpr)

    (stmts ++ retStmts, reg)
  }

  def runSubModule(field: FieldContainer)(implicit stack: StackFrame, ctx: FirrtlContext, global: GlobalData): (Vector[ir.Statement], ir.DefInstance) = {
    val stmts = field.code.flatMap(runStmt)
    val retStmts = field.ret
      .map(runExpr)
      .map{ case RunResult(stmts, _) => stmts }
      .getOrElse(throw new ImplementationErrorException("sub module instance expression must be there"))

    val tpeString = field.tpe.toFirrtlString
    val module = ir.DefInstance(ir.NoInfo, field.toFirrtlString, tpeString)

    (stmts ++ retStmts, module)
  }

  def runAlways(always: AlwaysContainer)(implicit stack: StackFrame, ctx: FirrtlContext, global: GlobalData): Vector[ir.Statement] = {
    always.code.flatMap(runStmt)
  }

  def buildStageSignature(stage: StageContainer)(implicit stack: StackFrame, global: GlobalData): Vector[ir.DefRegister] = {
    stage.params.foreach { case (name, _) => stack.lock(name) }
    val args = stage.params
      .map{ case (name, tpe) => stack.refer(name) -> tpe }
      .map{ case (name, tpe) => name -> HardInstance(tpe, ir.Reference(name.name, ir.UnknownType)) }
      .toVector

    args.foreach { case (name, instance) => stack.scope(name) = instance}

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

    val regs = args.map {
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

    (active +: regs) ++ state
  }

  def runStage(stage: StageContainer)(implicit stack: StackFrame, ctx: FirrtlContext, global: GlobalData): ir.Conditionally = {
    val stmts = stage.code.flatMap(runStmt)
    val states = stage.states.zipWithIndex.map {
      case (state, idx) =>
        val stateStmts = state.code.flatMap(runStmt)
        val stateRef = ir.Reference(stage.stateName, ir.UnknownType)
        ir.Conditionally(
          ir.NoInfo,
          ir.DoPrim(PrimOps.Eq, Seq(stateRef, ir.UIntLiteral(idx)), Seq.empty, ir.UnknownType),
          ir.Block(stateStmts),
          ir.EmptyStmt
        )
    }

    ir.Conditionally(
      ir.NoInfo,
      ir.Reference(stage.activeName, ir.UnknownType),
      ir.Block(stmts ++ states),
      ir.EmptyStmt
    )
  }

  def buildInterfaceSignature(interface: MethodContainer)(implicit stack: StackFrame, global: GlobalData): (Vector[ir.Port], Vector[ir.Statement]) = {
    interface.params.foreach { case (name, _) => stack.lock(name) }
    val args = interface.params
      .map{ case (name, tpe) => stack.refer(name) -> tpe }
      .map{ case (name, tpe) => name -> HardInstance(tpe, ir.Reference(name.name, ir.UnknownType)) }
      .toVector

    args.foreach { case (name, instance) => stack.scope(name) = instance }

    val isInputInterface =
      interface.label.symbol.hasFlag(Modifier.Input) ||
      interface.label.symbol.hasFlag(Modifier.Sibling)

    val paramWires =
      if(isInputInterface) args.map{ case (name, inst) => ir.Port(ir.NoInfo, name.name, ir.Input, toFirrtlType(inst.tpe))}
      else args.map{ case (name, inst) => ir.DefWire(ir.NoInfo, name.name, toFirrtlType(inst.tpe)) }

    val paramInvalids =
      if(isInputInterface) Vector.empty
      else args.map{ case (name, _) => ir.IsInvalid(ir.NoInfo, ir.Reference(name.name, ir.UnknownType)) }

    val active =
      if(isInputInterface) ir.Port(ir.NoInfo, interface.activeName, ir.Input, ir.UIntType(ir.IntWidth(1)))
      else ir.DefWire(ir.NoInfo, interface.activeName, ir.UIntType(ir.IntWidth(1)))

    val activeOff =
      if(isInputInterface) None
      else Some(ir.Connect(ir.NoInfo, ir.Reference(interface.activeName, ir.UnknownType), ir.UIntLiteral(0)))

    val isUnitRet = interface.label.symbol.tpe.asMethodType.returnType =:= Type.unitTpe
    val ret =
      if (isUnitRet) None
      else if(isInputInterface) Some(ir.Port(ir.NoInfo, interface.retName, ir.Output, toFirrtlType(interface.ret.tpe)))
      else Some(ir.DefWire(ir.NoInfo, interface.retName, toFirrtlType(interface.ret.tpe)))

    val retInvalid =
      if(isUnitRet) None
      else Some(ir.IsInvalid(ir.NoInfo, ir.Reference(interface.retName, ir.UnknownType)))

    if(isInputInterface) {
      val ports = (active.asInstanceOf[ir.Port] +: paramWires.map(_.asInstanceOf[ir.Port])) ++ ret.map(_.asInstanceOf[ir.Port])
      val stmts = activeOff ++ paramInvalids ++ retInvalid

      (ports, stmts.toVector)
    } else {
      val wires = (active.asInstanceOf[ir.DefWire] +: paramWires.map(_.asInstanceOf[ir.DefWire])) ++ ret.map(_.asInstanceOf[ir.DefWire])
      val stmts = activeOff ++ paramInvalids ++ retInvalid

      (Vector.empty, wires ++ stmts)
    }
  }

  def runInterface(interface: MethodContainer)(implicit stack: StackFrame, ctx: FirrtlContext, global: GlobalData): ir.Conditionally = {
    val stmts = interface.code.flatMap(runStmt(_))
    val RunResult(retStmts, instance) = runExpr(interface.ret)
    val methodRetTpe = interface.label.symbol.tpe.asMethodType.returnType
    val connect =
      if(methodRetTpe =:= Type.unitTpe) None
      else {
        val HardInstance(_, refer) = instance
        val connectTarget = ir.Reference(interface.retName, ir.UnknownType)
        val connect = ir.Connect(ir.NoInfo, connectTarget, refer)

        Some(connect)
      }

    ir.Conditionally(
      ir.NoInfo,
      ir.Reference(interface.activeName, ir.UnknownType),
      ir.Block(stmts ++ retStmts ++ connect),
      ir.EmptyStmt
    )
  }

  def buildUpperModule(moduleName: String, tpe: BackendType)(implicit ctx: FirrtlContext, global: GlobalData): (Vector[ir.Port], Vector[ir.Statement]) = {
    // This is same of ctx.interfaces.get(tpe).getOrElse(Vector.empty).
    // However, it does not work in expect.
    // That's why, for now, I get specific module's interface by below manner.
    val allInterfaces = ctx.interfaces
      .find { case (key, _) => key.hashCode == tpe.hashCode }
      .map{ case (_, value) => value }
      .getOrElse(Vector.empty)

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
        val paramInits = interface.params.keys
          .map(name => ir.IsInvalid(ir.NoInfo, ir.Reference(buildName(name), ir.UnknownType)))
          .toVector

        ((activePort +: paramPorts) ++ retPort, activeInit +: paramInits)
    }

    val (ports, inits) = pairs.unzip

    (ports.flatten, inits.flatten)
  }

  def runStmt(stmt: backend.Stmt)(implicit stack: StackFrame, ctx: FirrtlContext, global: GlobalData): Vector[ir.Statement] = {
    def buildConnect(name: Name, expr: backend.Expr)(connect: ir.Expression => Vector[ir.Statement]): (Instance, Vector[ir.Statement]) = {
      val RunResult(stmts, instance) = runExpr(expr)

      val (inst, defStmts) = instance match {
        case inst: SoftInstance => (inst, Vector.empty)
        case inst: HardInstance =>
          val connectStmts = connect(inst.reference)
          val wireInst = HardInstance(inst.tpe, ir.Reference(name.name, ir.UnknownType))
          (wireInst, connectStmts)
        case inst: ModuleInstance => (inst, Vector.empty)
      }

      (inst, stmts ++ defStmts)
    }

    stmt match {
      case backend.Variable(name, tpe, expr) =>
        val varName = stack.next(name)

        val (inst, stmts) = buildConnect(varName, expr){
          expr =>
            val firrtlType = toFirrtlType(tpe)
            val varDef = ir.DefWire(ir.NoInfo, varName.name, firrtlType)
            val connect = ir.Connect(ir.NoInfo, ir.Reference(varName.name, ir.UnknownType), expr)

            Vector(varDef, connect)
        }

        stack.scope(varName) = inst
        stmts
      case backend.Temp(id, expr) =>
        val tempName = stack.next(id)

        val (inst, stmts) = buildConnect(tempName, expr) {
          expr =>
            Vector(ir.DefNode(
              ir.NoInfo,
              tempName.name,
              expr
            ))
        }

        stack.scope(tempName) = inst
        stmts
      case backend.Assign(target, expr) =>
        val targetName = stack.refer(target.name)
        val HardInstance(_, rightRefer) = stack.scope(targetName)

        val RunResult(stmts, HardInstance(_, leftRefer)) = runExpr(expr)
        val connect = ir.Connect(ir.NoInfo, rightRefer, leftRefer)

        stmts :+ connect
      case backend.Return(expr) => ???
      case backend.Abandon(expr) =>
        val RunResult(stmts, _) = runExpr(expr)
        stmts
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
      case finish: backend.Finish => runFinish(finish)
      case goto: backend.Goto => runGoto(goto)
      case generate: backend.Generate => runGenerate(generate)
      case backend.IntLiteral(value) => RunResult(Vector.empty, IntInstance(value))
      case backend.UnitLiteral() => RunResult(Vector.empty, UnitInstance())
      case backend.StringLiteral(value) => RunResult(Vector.empty, StringInstance(value))
      case bit @ backend.BitLiteral(value, HPElem.Num(width)) =>
        RunResult(Vector.empty, BitInstance(bit.tpe, ir.UIntLiteral(value, ir.IntWidth(width))))
    }

  def runIdent(ident: backend.Ident)(implicit stack: StackFrame, ctx: FirrtlContext, global: GlobalData): RunResult = {
    val name = stack.refer(ident.id.name)
    RunResult(Vector.empty, stack.scope(name))
  }

  def runReferField(referField: backend.ReferField)(implicit stack: StackFrame, ctx: FirrtlContext, global: GlobalData): RunResult = {
    val accessor = referField.accessor match {
      case backend.Term.Temp(id, _) => stack.scope(stack.refer(id))
      case backend.Term.Variable(name, _) => stack.scope(stack.refer(name))
    }

    val instance = accessor match {
      case SoftInstance(_, fieldMap) => fieldMap(referField.field.toString)
      case HardInstance(_, refer) =>
        val subField = ir.SubField(refer, referField.field.toString, toFirrtlType(referField.tpe))
        UserHardInstance(referField.tpe, subField)
      case ModuleInstance(_, ModuleLocation.Sub(refer)) =>
        val subField = ir.SubField(refer, referField.field.toString, ir.UnknownType)
        val tpe = referField.tpe

        referField.field.symbol.tpe.asRefType.origin match {
          case _: Symbol.ModuleSymbol => throw new ImplementationErrorException("module instance must be referred directly")
          case _ => UserHardInstance(tpe, subField)
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
            UserHardInstance(tpe, reference)
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

      stack.scope(name)
    }

    val accessorTpe = call.accessor match {
      case Some(backend.Term.Temp(_, tpe)) => tpe
      case Some(backend.Term.Variable(_, tpe)) => tpe
    }

    val method = ctx.methods(accessorTpe).find(_.label == call.label).get
    val accessor = call.accessor.map(getInstance)
    val args = call.args.map(getInstance)
    val hargs = call.hargs.map {
      case HPElem.Num(value) => IntInstance(value)
      case HPElem.Str(value) => StringInstance(value)
    }

    val newStack = StackFrame(stack, accessor)

    val hargNames = method.hparams.keys.map(newStack.next)
    val argNames = method.params.keys.map(newStack.next)

    (hargNames zip hargs).foreach { case (name, harg) => newStack.scope(name) = harg }
    (argNames zip args).foreach { case (name, arg) => newStack.scope(name) = arg }

    val stmts = method.code.flatMap(stmt => runStmt(stmt)(newStack, ctx, global))
    val RunResult(retStmts, instance) = runExpr(method.ret)(newStack, ctx, global)

    RunResult(stmts ++ retStmts, instance)
  }

  def runCallInterface(call: backend.CallInterface)(implicit stack: StackFrame, ctx: FirrtlContext, global: GlobalData): RunResult = {
    def callInternal(tpe: BackendType): RunResult = {
      val candidates = ctx.interfaces(tpe)
      val interface = candidates.find(_.label == call.label).get
      val params = interface.params
        .map{ case (name, _) => stack.refer(name) }
        .map{ name => ir.Reference(name.name, ir.UnknownType) }

      val argNames = call.args.map {
        case backend.Term.Temp(id, _) => stack.refer(id)
        case backend.Term.Variable(name, _) => stack.refer(name)
      }
      val argInstances = argNames.map(stack.scope)
      val args = argInstances.map(_.asInstanceOf[HardInstance]).map(inst => inst.reference)

      val activate: ir.Statement = {
        val refer = ir.Reference(interface.activeName, ir.UnknownType)
        ir.Connect(ir.NoInfo, refer, ir.UIntLiteral(1))
      }
      val referReturn: Option[ir.Reference] = interface.ret match {
        case backend.UnitLiteral() => None
        case _ => Some(ir.Reference(interface.retName, ir.UnknownType))
      }

      val connects = (params zip args).map{ case (param, arg) => ir.Connect(ir.NoInfo, param, arg) }.toVector

      val instance = referReturn match {
        case None => UnitInstance()
        case Some(refer) => HardInstance(call.tpe, refer)
      }

      RunResult(activate +: connects, instance)
    }

    def callToSubModule(module: ir.Reference, tpe: BackendType): RunResult = {
      val candidates = ctx.interfaces(tpe)
      val interface = candidates.find(_.label == call.label).get
      val params = interface.params.map{ case (name, _) => ir.SubField(module, name, ir.UnknownType) }

      val argNames = call.args.map {
        case backend.Term.Temp(id, _) => stack.refer(id)
        case backend.Term.Variable(name, _) => stack.refer(name)
      }
      val args = argNames.map(stack.scope).map{ instance => instance match {
        case HardInstance(_, refer) => refer
      }}

      val activate: ir.Statement = {
        val subField = ir.SubField(module, interface.activeName, ir.UnknownType)
        ir.Connect(ir.NoInfo, subField, ir.UIntLiteral(1))
      }

      val referReturn: Option[ir.SubField] = interface.ret match {
        case backend.UnitLiteral() => None
        case _ => Some(ir.SubField(module, interface.retName, ir.UnknownType))
      }

      val connects = (params zip args).map{ case (p, a) => ir.Connect(ir.NoInfo, p, a) }.toVector

      val instance = referReturn match {
        case None => UnitInstance()
        case Some(refer) => HardInstance(call.tpe, refer)
      }

      RunResult(activate +: connects, instance)
    }

    def callToUpperModule(module: String, tpe: BackendType): RunResult = {
      val candidates = ctx.interfaces(tpe)
      val interface = candidates.find(_.label == call.label).get
      val params = interface.params.map{ case (name, _) => ir.Reference(module + "$" + name, ir.UnknownType) }

      val argNames = call.args.map {
        case backend.Term.Temp(id, _) => stack.refer(id)
        case backend.Term.Variable(name, _) => stack.refer(name)
      }
      val args = argNames.map(stack.scope).map{ case HardInstance(_, refer) => refer }

      val activate: ir.Statement = {
        val activeRef = ir.Reference(module + "$" + interface.activeName, ir.UnknownType)
        ir.Connect(ir.NoInfo, activeRef, ir.UIntLiteral(1))
      }

      val referReturn = interface.ret match {
        case backend.UnitLiteral() => None
        case _ => Some(ir.Reference(module+ "$" + interface.retName, ir.UnknownType))
      }

      val connects = (params zip args).map{ case (p, a) => ir.Connect(ir.NoInfo, p, a) }.toVector

      val instance = referReturn match {
        case None => UnitInstance()
        case Some(refer) => HardInstance(call.tpe, refer)
      }

      RunResult(activate +: connects, instance)
    }

    val referName = call.accessor match {
      case backend.Term.Temp(id, _) => stack.refer(id)
      case backend.Term.Variable(name, _) => stack.refer(name)
    }

    stack.scope(referName) match {
      case ModuleInstance(tpe, ModuleLocation.This) => callInternal(tpe)
      case ModuleInstance(tpe, ModuleLocation.Sub(refer)) => callToSubModule(refer, tpe)
      case ModuleInstance(tpe, ModuleLocation.Upper(refer)) => callToUpperModule(refer, tpe)
    }
  }

  def runCallBuiltIn(call: backend.CallBuiltIn)(implicit stack: StackFrame, ctx: FirrtlContext, global: GlobalData): RunResult = {
    def getInstance(term: backend.Term): Instance =
      term match {
        case backend.Term.Temp(id, _) => stack.scope(stack.refer(id))
        case backend.Term.Variable(name, _) => stack.scope(stack.refer(name))
      }

    val left = getInstance(call.args.head)
    val right = getInstance(call.args.tail.head)

    val instance = call.label match {
      case "_builtin_add_int_int" => builtin.intIntAdd(left, right, global)
      case "_builtin_sub_int_int" => builtin.intIntSub(left, right, global)
      case "_builtin_mul_int_int" => builtin.intIntMul(left, right, global)
      case "_builtin_div_int_int" => builtin.intIntDiv(left, right, global)
      case "_builtin_add_bit_bit" => builtin.bitBitAdd(left, right, global)
      case "_builtin_sub_bit_bit" => builtin.bitBitSub(left, right, global)
      case "_builtin_mul_bit_bit" => builtin.bitBitMul(left, right, global)
      case "_builtin_div_bit_bit" => builtin.bitBitDiv(left, right, global)
    }

    RunResult(Vector.empty, instance)
  }

  def runThis()(implicit stack: StackFrame, ctx: FirrtlContext, global: GlobalData): RunResult =
    RunResult(Vector.empty, stack.lookupThis.get)

  def runIfExpr(ifExpr: backend.IfExpr)(implicit stack: StackFrame, ctx: FirrtlContext, global: GlobalData): RunResult = {
    def runInner(stmts: Vector[backend.Stmt], last: backend.Expr): RunResult = {
      val innerStmts = stmts.flatMap(runStmt)
      val RunResult(lastStmts, instance) = runExpr(last)

      RunResult(innerStmts ++ lastStmts, instance)
    }

    def connectRet(wire: Option[ir.Reference], instance: Instance): Option[ir.Connect] =
      wire.flatMap { wire => instance match {
        case HardInstance(_, refer) => Some(ir.Connect(ir.NoInfo, wire, refer))
        case _: SoftInstance => None
      }}

    val condName = stack.refer(ifExpr.cond.id)
    stack.scope(condName) match {
      case BoolInstance(true) => runInner(ifExpr.conseq, ifExpr.conseqLast)
      case BoolInstance(false) => runInner(ifExpr.alt, ifExpr.altLast)
      case BitInstance(_, condRef) =>
        lazy val retName = stack.next("_IFRET")

        val retWire =
          if(ifExpr.tpe == toBackendType(Type.unitTpe, Map.empty, Map.empty)) None
          else Some(ir.DefWire(ir.NoInfo, retName.name, toFirrtlType(ifExpr.tpe)))

        val wireRef = retWire.map(wire => ir.Reference(wire.name, ir.UnknownType))

        val RunResult(conseqStmts, conseqInst) = runInner(ifExpr.conseq, ifExpr.conseqLast)
        val RunResult(altStmts, altInst) = runInner(ifExpr.alt, ifExpr.altLast)
        val conseqRet = connectRet(wireRef, conseqInst)
        val altRet = connectRet(wireRef, altInst)

        val whenStmt = ir.Conditionally (
          ir.NoInfo,
          condRef,
          ir.Block(conseqStmts ++ conseqRet),
          ir.Block(altStmts ++ altRet)
        )

        val retInstance = wireRef match {
          case None => UnitInstance()
          case Some(wireRef) => HardInstance(ifExpr.tpe, wireRef)
        }

        RunResult(retWire.toVector :+ whenStmt, retInstance)
    }
  }

  def runConstructStruct(construct: backend.ConstructStruct)(implicit stack: StackFrame, ctx: FirrtlContext, global: GlobalData): RunResult = {
    def constructHard(preStmts: Vector[ir.Statement], results: Map[String, RunResult]): RunResult = {
      val bundleType = toFirrtlType(construct.tpe)
      val bundleName = stack.next("_BUNDLE")
      val bundleRef = ir.Reference(bundleName.name, bundleType)
      val varDef = ir.DefWire(ir.NoInfo, bundleName.name, bundleType)
      val connects = results.mapValues(_.instance).map {
        case (name, HardInstance(_, expr)) =>
          val field = ir.SubField(bundleRef, name, expr.tpe)
          ir.Connect(ir.NoInfo, field, expr)
      }

      val stmts = varDef +: connects.toVector
      val refer = ir.Reference(bundleName.name, bundleType)
      val instance = UserHardInstance(construct.tpe, refer)

      RunResult(preStmts ++ stmts, instance)
    }

    def constructSoft(preStmts: Vector[ir.Statement], results: Map[String, RunResult]): RunResult = {
      val fieldElems = results.mapValues(_.instance)
      val instance = UserSoftInstance(construct.tpe, fieldElems)

      RunResult(preStmts, instance)
    }

    val results = construct.pairs.map { case (key, value) => key -> runExpr(value) }
    val stmts = results.values.foldLeft(Vector.empty[ir.Statement]) {
      case (stmts, result) => stmts ++ result.stmts
    }

    if(construct.target.isHardware) constructHard(stmts, results)
    else constructSoft(stmts, results)

  }

  def runConstructModule(construct: backend.ConstructModule)(implicit stack: StackFrame, ctx: FirrtlContext, global: GlobalData): RunResult = {
    val moduleName = construct.name match {
      case backend.Term.Variable(name, _) => Name(name)
      case backend.Term.Temp(id, _) => stack.next(id)
    }

    val moduleRef = ir.Reference(moduleName.name, ir.UnknownType)

    def buildIndirectAccessCond(interface: MethodContainer, fromName: String)(targetBuilder: String => ir.Expression): (Option[ir.IsInvalid], ir.Conditionally) = {
      val isUnitRet = interface.ret.tpe == toBackendType(Type.unitTpe)
      val targetActive = targetBuilder(interface.activeName)

      val targetRet =
        if(isUnitRet) None
        else Some(targetBuilder(interface.retName))

      val targetParams = interface.params.keys.map{ param => targetBuilder(param) }.toVector
      val targets = (targetActive +: targetParams)

      def fromRef(name: String): ir.SubField = ir.SubField(moduleRef, fromName + "$" + name, ir.UnknownType)
      val fromActive = fromRef(interface.activeName)

      val fromRet =
        if(isUnitRet) None
        else Some(fromRef(interface.retName))

      val retInvalid = fromRet.map(ret => ir.IsInvalid(ir.NoInfo, ret))

      val fromParams = interface.params.map { case (param, _) => fromRef(param) }.toVector
      val froms = (fromActive +: fromParams)

      val connects = (targets zip froms).map { case (target, from) => ir.Connect(ir.NoInfo, target, from) }
      val retConnect = (fromRet zip targetRet).map{ case (from, target) => ir.Connect(ir.NoInfo, from, target) }

      val cond = ir.Conditionally(
        ir.NoInfo,
        fromActive,
        ir.Block(connects ++ retConnect),
        ir.EmptyStmt
      )

      (retInvalid, cond)
    }

    val parentStmtsIter = construct.parents.flatMap {
      case (fromName, expr) =>
        val RunResult(stmts, ModuleInstance(tpe, refer)) = runExpr(expr)
        val parents = ctx.interfaces(tpe).filter(_.label.symbol.hasFlag(Modifier.Parent))

        val targetName: String => ir.Expression = refer match {
          case ModuleLocation.This => (name: String) => ir.Reference(name, ir.UnknownType)
          case ModuleLocation.Upper(target) => name: String => ir.Reference(target + "$" + name, ir.UnknownType)
          case _: ModuleLocation.Sub => throw new ImplementationErrorException("refer a sub module as a parent module")
        }

        val (invalids, conds) = parents.map(buildIndirectAccessCond(_, fromName)(targetName)).unzip

        stmts ++ invalids.flatten ++ conds
    }

    val siblingStmtsIter = construct.siblings.flatMap {
      case (fromName, expr) =>
        val RunResult(stmts, ModuleInstance(tpe, refer)) = runExpr(expr)
        val siblings = ctx.interfaces(tpe).filter(_.label.symbol.hasFlag(Modifier.Sibling))

        val target: String => ir.Expression = refer match {
          case ModuleLocation.This => throw new ImplementationErrorException("refer this module as sibling module")
          case ModuleLocation.Sub(refer) => (name: String) => ir.SubField(refer, name, ir.UnknownType)
          case ModuleLocation.Upper(refer) => (name: String) => ir.Reference(refer + "$" + name, ir.UnknownType)
        }

        val (invalid, conds) = siblings.map(buildIndirectAccessCond(_, fromName)(target)).unzip

        stmts ++ invalid.flatten ++ conds
    }

    val inputInits = ctx.interfaces(construct.tpe)
      .filter(interface => interface.label.symbol.hasFlag(Modifier.Input) || interface.label.symbol.hasFlag(Modifier.Sibling))
      .flatMap {
        interface =>
          def buildRef(name: String): ir.SubField = ir.SubField(moduleRef, name, ir.UnknownType)
          val activeRef = buildRef(interface.activeName)
          val paramRefs = interface.params.keys.map(buildRef)

          val activeOff = ir.Connect(ir.NoInfo, activeRef, ir.UIntLiteral(0))
          val paramInvalid = paramRefs.map(ir.IsInvalid(ir.NoInfo, _)).toVector

          activeOff +: paramInvalid
      }

    val connectClock = ir.Connect(ir.NoInfo, ir.SubField(moduleRef, clockName, ir.UnknownType), clockRef)
    val connectReset = ir.Connect(ir.NoInfo, ir.SubField(moduleRef, resetName, ir.UnknownType), resetRef)
    val parentStmts = parentStmtsIter.toVector
    val siblingStmts = siblingStmtsIter.toVector

    val stmts = Vector(connectClock, connectReset) ++ inputInits ++ parentStmts ++ siblingStmts

    RunResult(stmts, ModuleInstance(construct.tpe, ModuleLocation.Sub(ir.Reference(moduleName.name, ir.UnknownType))))
  }

  def runConstructEnum(enum: backend.ConstructEnum)(implicit stack: StackFrame, ctx: FirrtlContext, global: GlobalData): RunResult = {
    def constructHardEnum: RunResult = {
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
        .map(_.asInstanceOf[HardInstance])
        .flatMap(inst => splitValue(toFirrtlType(inst.tpe), inst.reference))
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
      val wireDef = ir.DefWire(ir.NoInfo, enumName.name, tpe)
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

      val runResultStmts = Vector(wireDef, connectFlag, connectData)
      val instance = HardInstance(enum.tpe, enumRef)

      RunResult(runResultStmts, instance)
    }

    def constructSoftEnum: RunResult = {
      val insts = enum.passed.map(temp => stack.lookup(stack.refer(temp.id)))
      val pairs = insts.zipWithIndex.map { case (inst, idx) => s"_$idx" -> inst }
      val table = ListMap.from(pairs)

      val instance = EnumSoftInstance(enum.target, enum.variant, table)

      RunResult(Vector.empty, instance)
    }

    if(enum.target.isHardware) constructHardEnum
    else constructSoftEnum
  }

  def runFinish(finish: backend.Finish)(implicit stack: StackFrame, ctx: FirrtlContext, global: GlobalData): RunResult = {
    val stageName = finish.stage.toString
    val active = stageName + "$_active"
    val activeRef = ir.Reference(active, ir.UnknownType)
    val finishStmt = ir.Connect(ir.NoInfo, activeRef, ir.UIntLiteral(0))

    RunResult(Vector(finishStmt), UnitInstance())
  }

  def runGoto(goto: backend.Goto)(implicit stack: StackFrame, ctx: FirrtlContext, global: GlobalData): RunResult = {
    val stateIndex = goto.state.index
    val stageState = goto.state.stage.toString + "$_state"
    val stateRef = ir.Reference(stageState, ir.UnknownType)
    val changeState = ir.Connect(ir.NoInfo, stateRef, ir.UIntLiteral(stateIndex))

    RunResult(Vector(changeState), UnitInstance())
  }

  def runGenerate(generate: backend.Generate)(implicit stack: StackFrame, ctx: FirrtlContext, global: GlobalData): RunResult = {
    val activeName = generate.stage.toString + "$_active"
    val activeRef = ir.Reference(activeName, ir.UnknownType)
    val argNames = generate.args.map {
      case backend.Term.Temp(id, _) => stack.refer(id)
      case backend.Term.Temp(name, _) => stack.refer(name)
    }
    val argRefs = argNames.map(name => ir.Reference(name.name, ir.UnknownType))

    val stageContainer = ctx.stages(stack.lookupThis.get.tpe).find(_.label == generate.stage).get
    val paramNames = stageContainer.params.keys.toVector
    val paramRefs = paramNames.map(name => ir.Reference(name, ir.UnknownType))

    val activate = ir.Connect(ir.NoInfo, activeRef, ir.UIntLiteral(1))
    val params = (paramRefs zip argRefs).map{ case (param, arg) => ir.Connect(ir.NoInfo, param, arg) }

    RunResult(activate +: params, UnitInstance())
  }

  def toFirrtlType(tpe: BackendType)(implicit global: GlobalData): ir.Type = {
    def toBitType: ir.UIntType = {
      val HPElem.Num(width) = tpe.hargs.head
      ir.UIntType(ir.IntWidth(width))
    }

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

    val types = global.builtin.types

    tpe.symbol match {
      case symbol if symbol == types.lookup("Bit") => toBitType
      case symbol: Symbol.EnumSymbol => toEnumType(symbol)
      case _ => toOtherType
    }
  }
}
