package tchdl.backend

import tchdl.util.{GlobalData, Symbol, Type}

import firrtl.ir
import scala.collection.immutable.ListMap

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
