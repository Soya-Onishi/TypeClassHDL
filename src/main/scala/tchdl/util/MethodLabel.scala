package tchdl.util

import tchdl.backend._

import scala.collection.immutable.ListMap

trait BackendLabel {
  type SymbolType <: Symbol.TermSymbol

  val symbol: SymbolType
  val accessor: BackendType
  val hps: ListMap[Symbol.HardwareParamSymbol, HPElem]
  val tps: ListMap[Symbol.TypeParamSymbol, BackendType]

  override def hashCode(): Int = symbol.hashCode + accessor.hashCode + hps.hashCode + tps.hashCode
}

case class MethodLabel(
  symbol: Symbol.MethodSymbol,
  accessor: BackendType,
  hps: ListMap[Symbol.HardwareParamSymbol, HPElem],
  tps: ListMap[Symbol.TypeParamSymbol, BackendType]
) extends BackendLabel {
  override type SymbolType = Symbol.MethodSymbol

  override def equals(obj: Any): Boolean = obj match {
    case that: MethodLabel =>
      this.symbol == that.symbol &&
      this.accessor == that.accessor &&
      this.hps == that.hps &&
      this.tps == that.tps
    case _ => false
  }
}

case class StageLabel(
  symbol: Symbol.StageSymbol,
  accessor: BackendType,
  hps: ListMap[Symbol.HardwareParamSymbol, HPElem],
  tps: ListMap[Symbol.TypeParamSymbol, BackendType]
) extends BackendLabel {
  override type SymbolType = Symbol.StageSymbol

  override def equals(obj: Any): Boolean = obj match {
    case that: StageLabel =>
      this.symbol == that.symbol &&
      this.accessor == that.accessor &&
      this.hps == that.hps &&
      this.tps == that.tps
    case _ => false
  }
}
