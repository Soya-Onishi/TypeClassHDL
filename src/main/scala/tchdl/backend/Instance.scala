package tchdl.backend

import tchdl.util.{GlobalData, Symbol, Type}
import firrtl.ir
import tchdl.util.TchdlException.ImplementationErrorException

trait Instance {
  type ReferType

  val tpe: BackendType
  def refer: ReferType
}

abstract class DataInstance extends Instance {
  override type ReferType = ir.Expression

  val tpe: BackendType
  def refer: ir.Expression
}

abstract class ModuleInstance extends Instance {
  override type ReferType = ModuleLocation

  val tpe: BackendType
  val refer: ModuleLocation
}

trait ModuleLocation
object ModuleLocation {
  case class Sub(refer: ir.Reference) extends ModuleLocation
  case class Upper(refer: String) extends ModuleLocation
  case object This extends ModuleLocation
}

object DataInstance {
  def apply(int: Int)(implicit global: GlobalData): StructInstance =
    StructInstance(toBackendType(Type.intTpe), ir.UIntLiteral(int, ir.IntWidth(32)))

  def apply(bool: Boolean)(implicit global: GlobalData): StructInstance = {
    val value = if(bool) 1 else 0
    StructInstance(toBackendType(Type.boolTpe), ir.UIntLiteral(value, ir.IntWidth(1)))
  }

  def apply()(implicit global: GlobalData): StructInstance =
    StructInstance(toBackendType(Type.unitTpe), ir.UIntLiteral(0, ir.IntWidth(0)))

  def apply(tpe: BackendType, variant: Option[Symbol.EnumMemberSymbol], refer: ir.Expression): EnumInstance =
    EnumInstance(tpe, variant, refer)

  def apply(tpe: BackendType, refer: ir.Expression): StructInstance =
    StructInstance(tpe, refer)

  def unapply(obj: Any): Option[(BackendType, ir.Expression)] =
    obj match {
      case instance: DataInstance => Some(instance.tpe, instance.refer)
      case _ => None
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


case class EnumInstance(tpe: BackendType, variant: Option[Symbol.EnumMemberSymbol], refer: ir.Expression) extends DataInstance
case class StructInstance(tpe: BackendType, refer: ir.Expression) extends DataInstance
case class StringInstance(value: String)(implicit global: GlobalData) extends DataInstance {
  val field = Map.empty
  val tpe = toBackendType(Type.stringTpe, Map.empty, Map.empty)
  def refer = throw new ImplementationErrorException("refer string instance")
}

// case class BitInstance(tpe: BackendType, refer: ir.Expression) extends DataInstance

/*
case class IntInstance(refer: ir.Expression)(implicit global: GlobalData) extends DataInstance {
  val field = Map.empty
  val tpe = toBackendType(Type.intTpe, Map.empty, Map.empty)
}
object IntInstance {
  def apply(value: Int)(implicit global: GlobalData): IntInstance = {
    IntInstance(ir.UIntLiteral(value, ir.IntWidth(32)))
  }
}
*/

/*
case class BoolInstance()(implicit global: GlobalData) extends DataInstance {
  val field = Map.empty
  val tpe = toBackendType(Type.boolTpe, Map.empty, Map.empty)
}

object BoolInstance {
  def apply(value: Boolean): BoolInstance = {
    val num = if (value) 1 else 0
    val refer = ir.UIntLiteral(num, ir.IntWidth(1))

  }
}

case class UnitInstance()(implicit global: GlobalData) extends DataInstance {
  val field = Map.empty
  val tpe = toBackendType(Type.unitTpe, Map.empty, Map.empty)
  val refer = ir.UIntLiteral(0, ir.IntWidth(0))
}
*/