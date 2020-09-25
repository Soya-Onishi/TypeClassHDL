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
  override type ReferType = lir.Expr

  val tpe: BackendType
  def refer: lir.Expr
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
  def apply(int: Int)(implicit global: GlobalData): StructInstance = {
    val intTpe = toBackendType(Type.bitTpe(32))
    StructInstance(intTpe, lir.Literal(BigInt(int), 32, intTpe))
  }

  def apply(bool: Boolean)(implicit global: GlobalData): StructInstance = {
    val value = if(bool) 1 else 0
    val tpe = toBackendType(Type.bitTpe(1))
    StructInstance(tpe, lir.Literal(value, 1, tpe))
  }

  def apply()(implicit global: GlobalData): StructInstance = {
    val tpe = toBackendType(Type.unitTpe)
    StructInstance(tpe, lir.Literal(0, 0, tpe))
  }

  def apply(tpe: BackendType, variant: Option[Symbol.EnumMemberSymbol], refer: lir.Expr): EnumInstance =
    EnumInstance(tpe, variant, refer)

  def apply(tpe: BackendType, refer: lir.Expr): StructInstance =
    StructInstance(tpe, refer)

  def unapply(obj: DataInstance): Option[(BackendType, lir.Expr)] = Some(obj.tpe, obj.refer)
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


case class EnumInstance(tpe: BackendType, variant: Option[Symbol.EnumMemberSymbol], refer: lir.Expr) extends DataInstance
case class StructInstance(tpe: BackendType, refer: lir.Expr) extends DataInstance
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