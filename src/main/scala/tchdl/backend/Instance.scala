package tchdl.backend

import tchdl.util.{GlobalData, Symbol, Type}
import tchdl.backend.ast.{BackendLIR => lir}
import tchdl.util.TchdlException.ImplementationErrorException

trait Instance {
  type ReferType

  val tpe: BackendType
  def refer: ReferType
}

abstract class DataInstance extends Instance {
  override type ReferType = lir.Ref

  val tpe: BackendType
  def refer: lir.Ref
}

abstract class ModuleInstance extends Instance {
  override type ReferType = ModuleLocation

  val tpe: BackendType
  val refer: ModuleLocation
}

trait ModuleLocation
object ModuleLocation {
  case class Sub(refer: lir.Reference) extends ModuleLocation
  case class Upper(refer: String) extends ModuleLocation
  case object This extends ModuleLocation
}

object DataInstance {
  def int(int: Int)(implicit stack: StackFrame, global: GlobalData): RunResult = {
    val intTpe = BackendType.intTpe
    val (node, ref) = makeNode(lir.Literal(BigInt(int), intTpe))
    val inst = StructInstance(intTpe, ref)

    RunResult(Vector(node), inst)
  }

  def bool(bool: Boolean)(implicit stack: StackFrame, global: GlobalData): RunResult = {
    val tpe = BackendType.boolTpe
    val value = if(bool) 1 else 0
    val (node, ref) = makeNode(lir.Literal(value, tpe))
    val inst = StructInstance(tpe, ref)

    RunResult(Vector(node), inst)
  }

  def unit()(implicit stack: StackFrame, global: GlobalData): RunResult = {
    val tpe = BackendType.unitTpe
    val (node, ref) = makeNode(lir.Literal(0, tpe))
    val inst = StructInstance(tpe, ref)

    RunResult(Vector.empty, inst)
  }

  def apply(tpe: BackendType, variant: Option[Symbol.EnumMemberSymbol], refer: lir.Ref): EnumInstance =
    EnumInstance(tpe, variant, refer)

  def apply(tpe: BackendType, refer: lir.Ref): StructInstance =
    StructInstance(tpe, refer)

  def unapply(obj: DataInstance): Option[(BackendType, lir.Ref)] = Some(obj.tpe, obj.refer)

  private def makeNode(expr: lir.Expr)(implicit stack: StackFrame): (lir.Node, lir.Reference) = {
    val node = lir.Node(
      stack.next("_GEN").name,
      expr,
      expr.tpe
    )
    val ref = lir.Reference(node.name, node.tpe)

    (node, ref)
  }
}

object ModuleInstance {
  def apply(module: BackendType, refer: ModuleLocation): ModuleInstance = {
    val _refer = refer

    new ModuleInstance {
      val refer = _refer
      val tpe = module
    }
  }

  def unapply(obj: Any): Option[(BackendType, ModuleLocation)] =
    obj match {
      case inst: ModuleInstance => Some(inst.tpe, inst.refer)
      case _ => None
    }
}


case class EnumInstance(tpe: BackendType, variant: Option[Symbol.EnumMemberSymbol], refer: lir.Ref) extends DataInstance
case class StructInstance(tpe: BackendType, refer: lir.Ref) extends DataInstance
case class StringInstance(value: String)(implicit global: GlobalData) extends DataInstance {
  val field = Map.empty
  val tpe = toBackendType(Type.stringTpe, Map.empty, Map.empty)
  def refer = throw new ImplementationErrorException("refer string instance")
}