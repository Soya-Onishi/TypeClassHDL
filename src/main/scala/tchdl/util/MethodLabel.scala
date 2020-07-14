package tchdl.util

import tchdl.backend._

import scala.collection.immutable.ListMap

trait BackendLabel {
  type SymbolType <: Symbol.TermSymbol

  val symbol: SymbolType
  val accessor: Option[BackendType]
  val hps: ListMap[Symbol.HardwareParamSymbol, HPElem]
  val tps: ListMap[Symbol.TypeParamSymbol, BackendType]

  override def equals(obj: Any): Boolean = obj match {
    case that: BackendLabel =>
      this.symbol == that.symbol &&
      this.accessor == that.accessor &&
      this.hps == that.hps &&
      this.tps == that.tps
    case _ => false
  }

  override def hashCode(): Int = symbol.hashCode + accessor.hashCode + hps.hashCode + tps.hashCode
}

case class MethodLabel(
  symbol: Symbol.MethodSymbol,
  accessor: Option[BackendType],
  interface: Option[BackendType],
  hps: ListMap[Symbol.HardwareParamSymbol, HPElem],
  tps: ListMap[Symbol.TypeParamSymbol, BackendType]
) extends BackendLabel {
  def activeName: String = toString + "$_active"
  def retName: String = toString + "$_ret"

  override type SymbolType = Symbol.MethodSymbol

  override lazy val toString: String = {
    val interface = this.interface.map(_.symbol.name + "__").getOrElse("")
    val name = symbol.name

    interface + name + "_" + hashCode().toHexString
  }
}

case class StageLabel(
  symbol: Symbol.StageSymbol,
  accessor: Option[BackendType],
  hps: ListMap[Symbol.HardwareParamSymbol, HPElem],
  tps: ListMap[Symbol.TypeParamSymbol, BackendType]
) extends BackendLabel {
  def activeName: String = toString + "$_active"
  def retName: String = toString + "$_ret"
  def stateName: String = toString + "$_state"

  override type SymbolType = Symbol.StageSymbol
  override lazy val toString: String = symbol.name + "_" + hashCode().toHexString
}

case class StateLabel(
  symbol: Symbol.StateSymbol,
  accessor: Option[BackendType],
  stage: StageLabel,
  index: Int,
  hps: ListMap[Symbol.HardwareParamSymbol, HPElem],
  tps: ListMap[Symbol.TypeParamSymbol, BackendType]
) extends BackendLabel {
  override type SymbolType = Symbol.StateSymbol
  override lazy val toString: String = stage.toString + "$" + symbol.name
}

case class AlwaysLabel(
  symbol: Symbol.AlwaysSymbol,
  accessor: Option[BackendType],
  hps: ListMap[Symbol.HardwareParamSymbol, HPElem],
  tps: ListMap[Symbol.TypeParamSymbol, BackendType]
) extends BackendLabel {
  override type SymbolType = Symbol.AlwaysSymbol
  override lazy val toString: String = symbol.name
}

case class FieldLabel(
  symbol: Symbol.VariableSymbol,
  accessor: Option[BackendType],
  hps: ListMap[Symbol.HardwareParamSymbol, HPElem],
  tps: ListMap[Symbol.TypeParamSymbol, BackendType]
) extends BackendLabel {
  override type SymbolType = Symbol.VariableSymbol
  override lazy val toString: String = symbol.name
}
