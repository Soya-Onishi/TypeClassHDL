package tchdl.backend

import tchdl.backend.{ast => backend}
import tchdl.util._
import tchdl.util.TchdlException._
import firrtl.ir

import scala.annotation.tailrec
import scala.collection.immutable.ListMap
import scala.collection.mutable


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
    val refer: Option[ir.Reference]
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
    def apply(module: ModuleContainer)(implicit global: GlobalData): ModuleInstance = {
      /*
      val fields = module.fields.map{
        field =>
          val refer = ir.Reference(field.symbol.name, ir.UnknownType)
          field.symbol.name -> HardInstance(field.tpe, refer)
      }.toMap
       */

      new ModuleInstance {
        val refer = None
        val tpe = module.tpe

        override def isHardware: Boolean = false
      }
    }

    def unapply(obj: Any): Option[(BackendType, Option[ir.Reference])] =
      obj match {
        case inst: ModuleInstance => Some(inst.tpe, inst.refer)
        case _ => None
      }
  }

  case class UserSoftInstance(tpe: BackendType, field: Map[String, Instance]) extends SoftInstance
  case class IntInstance(value: Int)(implicit global: GlobalData) extends SoftInstance {
    val field = Map.empty
    val tpe = convertToBackendType(Type.intTpe, Map.empty, Map.empty)
  }

  case class StringInstance(value: String)(implicit global: GlobalData) extends SoftInstance {
    val field = Map.empty
    val tpe = convertToBackendType(Type.stringTpe, Map.empty, Map.empty)
  }

  case class BoolInstance(value: Boolean)(implicit global: GlobalData) extends SoftInstance {
    val field = Map.empty
    val tpe = convertToBackendType(Type.boolTpe, Map.empty, Map.empty)
  }

  case class UnitInstance()(implicit global: GlobalData) extends SoftInstance {
    val field = Map.empty
    val tpe = convertToBackendType(Type.unitTpe, Map.empty, Map.empty)
  }

  case class UserHardInstance(tpe: BackendType, reference: ir.Expression) extends HardInstance
  case class BitInstance(tpe: BackendType, reference: ir.Expression) extends HardInstance

  case class FirrtlContext(
    thisTerm: Option[Instance],
    interfaces: Map[BackendType, Vector[MethodContainer]],
    methods: Map[BackendType, Vector[MethodContainer]],
    namer: FirrtlNamer
  ) {
    val scope: mutable.Map[Name, Instance] = mutable.Map()
  }

  trait StackFrame {
    protected def parent: StackFrame

    def scope: mutable.Map[Name, Instance] = mutable.Map.empty
    def namer: FirrtlNamer

    val lookupThis: Option[Instance]

    def lookup(name: Name): Instance
    def assert(id: Name, instance: Instance): Unit

    final def next(name: String): Name = {
      count(name)
      refer(name)
    }

    final def next(id: Int): Name = {
      count(id)
      refer(id)
    }

    final def refer(name: String): Name = namer.variable.refer(name)
    final def refer(id: Int): Name = namer.temp.refer(id)

    @tailrec final protected def count(name: String): Unit = {
      if(parent != null) {
        namer.variable.next(name)
        parent.count(name)
      }
    }

    @tailrec final protected def count(id: Int): Unit = {
      if(parent != null) {
        namer.temp.next(id)
        parent.count(id)
      }
    }
  }

  abstract class Stack extends StackFrame {
    override def lookup(name: Name): Instance = scope.get(name) match {
      case Some(instance) => instance
      case None => throw new ImplementationErrorException("instance must be there")
    }

    override def assert(name: Name, instance: Instance): Unit = {
      scope(name) = instance
    }
  }

  object Stack {
    def apply(parent: StackFrame, thisTerm: Option[Instance]): Stack = {
      val _parent = parent

      new Stack {
        override val namer = _parent.namer.copy
        override val parent = _parent
        override val lookupThis = thisTerm
      }
    }
  }

  abstract class WeakStack extends StackFrame {
    override def lookup(name: Name): Instance =
      scope.get(name) match {
        case Some(instance) => instance
        case None => parent.lookup(name)
      }

    override def assert(name: Name, instance: Instance): Unit = {
      scope(name) = instance
    }
  }

  object WeakStack {
    def apply(parent: StackFrame): WeakStack = {
      val _parent = parent

      new WeakStack {
        override val namer = _parent.namer.copy
        override val parent = _parent
        override val lookupThis = _parent.lookupThis
      }
    }
  }

  class FirrtlNamer {
    private abstract class Counter[T] {
      protected val table: mutable.Map[T, Int] = mutable.Map.empty

      def next(key: T): Name
      def refer(key: T): Name
    }

    val temp: Counter[Int] = new Counter[Int] {
      private var max = 0

      def next(key: Int): Name = {
        val nextMax = max + 1
        table(key) = nextMax
        max = nextMax

        Name(s"TEMP_$nextMax")
      }

      def refer(key: Int): Name = {
        val value = table(key)

        Name(s"TEMP_$value")
      }
    }

    val variable: Counter[String] = new Counter[String] {
      def next(key: String): Name =
        table.get(key) match {
          case Some(count) =>
            table(key) = count + 1
            Name(s"${key}_$count")
          case None =>
            table(key) = 0
            Name(s"${key}_0")
        }

      def refer(key: String): Name = {
        val count = table(key)
        Name(s"${key}_$count")
      }
    }

    def copy: FirrtlNamer = ???
  }

  case class Name(name: String) {
    override def hashCode() = name.hashCode
  }

  case class RunResult(stmts: Vector[ir.Statement], instance: Instance)

  def exec(modules: Vector[ModuleContainer], methods: Vector[MethodContainer]): ir.Circuit = {
    ???
  }

  def buildModule(module: ModuleContainer, interfaces: Map[BackendType, Vector[MethodContainer]], methods: Map[BackendType, Vector[MethodContainer]])(implicit global: GlobalData): ir.Module = {
    val instance = ModuleInstance(module)

    val ctx = FirrtlContext(Some(instance), interfaces, methods, new FirrtlNamer)
    val (fieldStmts, fields) = module.fields.map(runField(_)(ctx, global)).unzip
    val alwaysStmts = module.always.flatMap(runAlways(_)(ctx, global))
    val interfaceConds = module.interfaces.map(runInterface(_)(ctx, global))
    // val stages = module.stages.map(runStage(_)(ctx, global))

    val groupedFields = fields.groupBy(_.getClass)
    val ports = groupedFields(ir.Port.getClass).map{ case port: ir.Port => port }
    val regs = groupedFields(ir.DefRegister.getClass).map { case reg: ir.DefRegister => reg }
    val wires = groupedFields(ir.DefWire.getClass).map{ case wire: ir.DefWire => wire }

    ir.Module(
      ir.NoInfo,
      module.tpe.toFirrtlString,
      ports,
      ir.Block(wires ++ fieldStmts.flatten ++ regs ++ alwaysStmts ++ interfaceConds)
    )
  }

  def runField(field: FieldContainer)(implicit ctx: FirrtlContext, global: GlobalData): (Vector[ir.Statement], ir.FirrtlNode) = {
    val fieldCtx = ctx.copy()
    val stmts = field.code.flatMap(runStmt(_)(fieldCtx, global))

    val (connectStmts, retRefer) = field.ret.map(runExpr(_)(fieldCtx, global))
      .map { case RunResult(retStmts, HardInstance(_, refer)) => (retStmts, Some(refer)) }
      .getOrElse((Vector.empty, None))

    val firrtlType = convertToFirrtlType(field.tpe)

    field.flag match {
      case flag if flag.hasFlag(Modifier.Input) =>
        val port = ir.Port(ir.NoInfo, field.symbol.name, ir.Input, firrtlType)
        val connect = retRefer.map(ir.Connect(ir.NoInfo, ir.Reference(field.symbol.name, ir.UnknownType), _))

        (stmts ++ connectStmts ++ connect, port)
      case flag if flag.hasFlag(Modifier.Internal) =>
        val wire = ir.DefWire(ir.NoInfo, field.symbol.name, firrtlType)
        val connect = retRefer.map(ir.Connect(ir.NoInfo, ir.Reference(field.symbol.name, ir.UnknownType), _))

        (stmts ++ connectStmts ++ connect, wire)
      case flag if flag.hasFlag(Modifier.Output) =>
        val port = ir.Port(ir.NoInfo, field.symbol.name, ir.Output, firrtlType)
        val last = retRefer
          .map(ir.Connect(ir.NoInfo, ir.Reference(field.symbol.name, ir.UnknownType), _))
          .getOrElse(ir.IsInvalid(ir.NoInfo, ir.Reference(field.symbol.name, ir.UnknownType)))

        (stmts ++ connectStmts :+ last, port)
      case flag if flag.hasFlag(Modifier.Register) =>
        val initExpr = retRefer match {
          case Some(refer) => refer
          case None => ir.Reference(field.symbol.name, ir.UnknownType)
        }

        val reg = ir.DefRegister(ir.NoInfo, field.symbol.name, firrtlType, clockRef, resetRef, initExpr)

        (stmts, reg)
    }
  }

  def runAlways(always: AlwaysContainer)(implicit ctx: FirrtlContext, global: GlobalData): Vector[ir.Statement] = {
    val alwaysCtx = ctx.copy()
    always.code.flatMap(runStmt(_)(alwaysCtx, global))
  }

  def runStage(stage: StageContainer)(implicit ctx: FirrtlContext, global: GlobalData): ir.Conditionally = {
    ???
  }

  def runInterface(interface: MethodContainer)(implicit ctx: FirrtlContext, global: GlobalData): ir.Conditionally = {
    val interfaceName = interface.toFirrtlString

    val args = interface.args
      .map{ case (name, tpe) => (interfaceName + "$" + name) -> tpe}
      .map{ case (name, tpe) => ctx.namer.variable.next(name) -> tpe }
      .map{ case (name, tpe) => name -> HardInstance(tpe, ir.Reference(name.name, ir.UnknownType)) }

    val hargInstances = interface.label.hps.values.map {
      case HPElem.Num(num) => IntInstance(num)
      case HPElem.Str(str) => StringInstance(str)
    }
    val hargNames = interface.hargs.keys
      .map(name => interfaceName + "$" + name)
      .map(ctx.namer.variable.next)

    val hargs = hargNames zip hargInstances

    val interfaceCtx = ctx.copy()

    args.foreach { case (name, instance) => interfaceCtx.scope(name) = instance }
    hargs.foreach { case (name, instance) => interfaceCtx.scope(name) = instance }

    val stmts = interface.code.flatMap(runStmt(_)(interfaceCtx, global))
    val RunResult(retStmts, instance) = runExpr(interface.ret)(interfaceCtx, global)
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

  def runStmt(stmt: backend.Stmt)(implicit ctx: FirrtlContext, global: GlobalData): Vector[ir.Statement] = {
    def buildConnect(name: Name, expr: backend.Expr)(connect: ir.Expression => Vector[ir.Statement]): (Instance, Vector[ir.Statement]) = {
      val RunResult(stmts, instance) = runExpr(expr)

      val (inst, defStmts) = instance match {
        case inst: SoftInstance => (inst, Vector.empty)
        case inst: HardInstance =>
          val connectStmts = connect(inst.reference)
          val wireInst = HardInstance(inst.tpe, ir.Reference(name.name, ir.UnknownType))
          (wireInst, connectStmts)
      }

      (inst, stmts ++ defStmts)
    }

    stmt match {
      case backend.Variable(name, tpe, expr) =>
        val varName = ctx.namer.variable.next(name)

        val (inst, stmts) = buildConnect(varName, expr){
          expr =>
            val firrtlType = convertToFirrtlType(tpe)
            val varDef = ir.DefWire(ir.NoInfo, varName.name, firrtlType)
            val connect = ir.Connect(ir.NoInfo, ir.Reference(varName.name, ir.UnknownType), expr)

            Vector(varDef, connect)
        }

        ctx.scope(varName) = inst
        stmts
      case backend.Temp(id, expr) =>
        val tempName = ctx.namer.temp.next(id)

        val (_, stmts) = buildConnect(tempName, expr) {
          expr =>
            Vector(ir.Connect(
              ir.NoInfo,
              ir.Reference(tempName.name, ir.UnknownType),
              expr
            ))
        }

        stmts
      case backend.Assign(target, expr) =>
        val targetName = ctx.namer.variable.refer(target.name)
        val HardInstance(_, rightRefer) = ctx.scope(targetName)

        val RunResult(stmts, HardInstance(_, leftRefer)) = runExpr(expr)
        val connect = ir.Connect(ir.NoInfo, rightRefer, leftRefer)

        stmts :+ connect
      case backend.Return(expr) => ???
    }
  }


  def runExpr(expr: backend.Expr)(implicit ctx: FirrtlContext, global: GlobalData): RunResult =
    expr match {
      case ident: backend.Ident => runIdent(ident)
      case refer: backend.ReferField => runReferField(refer)
      case ths: backend.This => runThis()
      case construct: backend.ConstructStruct => runConstructStruct(construct)
      case construct: backend.ConstructModule => ???
      case call: backend.CallMethod => runCallMethod(call)
      case call: backend.CallInterface => runCallInterface(call)
      case call: backend.CallBuiltIn => runCallBuiltIn(call)
      case ifExpr: backend.IfExpr => runIfExpr(ifExpr)
      case backend.IntLiteral(value) => RunResult(Vector.empty, IntInstance(value))
      case backend.UnitLiteral() => RunResult(Vector.empty, UnitInstance())
      case backend.StringLiteral(value) => RunResult(Vector.empty, StringInstance(value))
      case bit @ backend.BitLiteral(value, HPElem.Num(width)) =>
        RunResult(Vector.empty, BitInstance(bit.tpe, ir.UIntLiteral(value, ir.IntWidth(width))))
    }

  def runIdent(ident: backend.Ident)(implicit ctx: FirrtlContext, global: GlobalData): RunResult = {
    val name = ctx.namer.variable.refer(ident.id.name)
    RunResult(Vector.empty, ctx.scope(name))
  }

  def runReferField(referField: backend.ReferField)(implicit ctx: FirrtlContext, global: GlobalData): RunResult = {
    val accessor = referField.accessor match {
      case backend.Term.Temp(id, _) => ctx.scope(ctx.namer.temp.refer(id))
      case backend.Term.Variable(name, _) => ctx.scope(ctx.namer.variable.refer(name))
    }

    val instance = accessor match {
      case SoftInstance(_, fieldMap) => fieldMap(referField.field)
      case HardInstance(_, refer) =>
        val subField = ir.SubField(refer, referField.field, convertToFirrtlType(referField.tpe))
        UserHardInstance(referField.tpe, subField)
      case ModuleInstance(_, Some(refer)) =>
        val subField = ir.SubField(refer, referField.field, ir.UnknownType)
        UserHardInstance(referField.tpe, subField)
      case ModuleInstance(_, None) =>
        val reference = ir.Reference(referField.field, ir.UnknownType)
        UserHardInstance(referField.tpe, reference)
    }

    RunResult(Vector.empty, instance)
  }

  def runCallMethod(call: backend.CallMethod)(implicit ctx: FirrtlContext, global: GlobalData): RunResult = {
    def getInstance(term: backend.Term): Instance = {
      val name = term match {
        case backend.Term.Temp(id, _) => ctx.namer.temp.refer(id)
        case backend.Term.Variable(name, _) => ctx.namer.variable.refer(name)
      }

      ctx.scope(name)
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

    val newCtx = ctx.copy(thisTerm = accessor)

    val hargNames = method.hargs.keys
      .map(name => method.toFirrtlString + "$" + name)
      .map(ctx.namer.variable.next)

    val argNames = method.args.keys
      .map(name => method.toFirrtlString + "$" + name)
      .map(ctx.namer.variable.next)

    (hargNames zip hargs).foreach { case (name, harg) => newCtx.scope(name) = harg }
    (argNames zip args).foreach { case (name, arg) => newCtx.scope(name) = arg }

    val stmts = method.code.flatMap(stmt => runStmt(stmt)(newCtx, global))
    val RunResult(retStmts, instance) = runExpr(method.ret)(newCtx, global)

    RunResult(stmts ++ retStmts, instance)
  }

  def runCallInterface(call: backend.CallInterface)(implicit ctx: FirrtlContext, global: GlobalData): RunResult = {
    def callInternal(tpe: BackendType): RunResult = {
      val candidates = ctx.interfaces(tpe)
      val interface = candidates.find(_.label == call.label).get
      val params = interface.args.map(arg => ir.Reference(arg.name, convertToFirrtlType(arg.tpe)))
      val argNames = call.args.map {
        case backend.Term.Temp(id, _) => ctx.namer.temp.refer(id)
        case backend.Term.Variable(name, _) => ctx.namer.variable.refer(name)
      }
      val argInstances = argNames.map(ctx.scope)
      val args = argInstances.map(_.asInstanceOf[HardInstance]).map(inst => inst.reference)

      val activate: ir.Statement = ???
      val connects = (params zip args).map{ case (param, arg) => ir.Connect(ir.NoInfo, param, arg) }
      val referReturn: Option[ir.Reference] = ???
      val instance = referReturn match {
        case None => UnitInstance()
        case Some(refer) => HardInstance(call.tpe, refer)
      }

      RunResult(activate +: connects, instance)
    }

    def callExternal(module: ir.Reference, tpe: BackendType): RunResult = {
      val candidates = ctx.interfaces(tpe)
      val interface = candidates.find(_.label == call.label).get
      val params = interface.args.map(arg => ir.SubField(module, arg.name, ir.UnknownType))
      val argNames = call.args.map {
        case backend.Term.Temp(id, _) => ctx.namer.temp.refer(id)
        case backend.Term.Variable(name, _) => ctx.namer.variable.refer(name)
      }
      val args = argNames.map(ctx.scope).map{ case HardInstance(_, refer) => refer }

      val activate: ir.Statement = ???
      val connects = (params zip args).map{ case (p, a) => ir.Connect(ir.NoInfo, p, a) }
      val referReturn: Option[ir.Reference] = ???
      val instance = referReturn match {
        case None => UnitInstance()
        case Some(refer) => HardInstance(call.tpe, refer)
      }

      RunResult(activate +: connects, instance)
    }

    val referName = call.accessor match {
      case backend.Term.Temp(id, _) => ctx.namer.temp.refer(id)
      case backend.Term.Variable(name, _) => ctx.namer.variable.refer(name)
    }

    ctx.scope(referName) match {
      case ModuleInstance(tpe, Some(refer)) => callExternal(refer, tpe)
      case ModuleInstance(tpe, None) => callInternal(tpe)
    }
  }

  def runCallBuiltIn(call: backend.CallBuiltIn)(implicit ctx: FirrtlContext, global: GlobalData): RunResult = {
    val instance = call.label match {
      case _ => ???
    }

    RunResult(Vector.empty, instance)
  }

  def runThis()(implicit ctx: FirrtlContext, global: GlobalData): RunResult =
    RunResult(Vector.empty, ctx.thisTerm.get)

  def runIfExpr(ifExpr: backend.IfExpr)(implicit ctx: FirrtlContext, global: GlobalData): RunResult = {
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

    val condName = ctx.namer.temp.refer(ifExpr.cond.id)
    ctx.scope(condName) match {
      case BoolInstance(true) => runInner(ifExpr.conseq, ifExpr.conseqLast)
      case BoolInstance(false) => runInner(ifExpr.alt, ifExpr.altLast)
      case BitInstance(_, condRef) =>
        lazy val retName = ctx.namer.variable.next("_IFRET")

        val retWire =
          if(ifExpr.tpe == convertToBackendType(Type.unitTpe, Map.empty, Map.empty)) None
          else Some(ir.DefWire(ir.NoInfo, retName.name, convertToFirrtlType(ifExpr.tpe)))

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

  def runConstructStruct(construct: backend.ConstructStruct)(implicit ctx: FirrtlContext, global: GlobalData): RunResult = {
    def constructHard(preStmts: Vector[ir.Statement], results: Map[String, RunResult]): RunResult = {
      val bundleType = convertToFirrtlType(construct.tpe)
      val bundleName = ctx.namer.variable.next("_BUNDLE")
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

  def convertToFirrtlType(tpe: BackendType)(implicit global: GlobalData): ir.Type = {
    val types = global.builtin.types

    tpe.symbol match {
      case symbol if symbol == types.lookup("Bit") =>
        val HPElem.Num(width) = tpe.hargs.head
        ir.UIntType(ir.IntWidth(width))
      case _ =>
        val fields = tpe.fields
          .map{ case (name, tpe) => name -> convertToFirrtlType(tpe) }
          .toVector
          .sortWith{ case ((left, _), (right, _)) => left < right }
          .map{ case (name, tpe) => ir.Field(name, ir.Default, tpe) }

        ir.BundleType(fields)
    }
  }
}
