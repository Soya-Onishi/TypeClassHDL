package tchdl.util

import tchdl.backend._

import scala.collection.immutable.ListMap

trait BackendLabel {
  type SymbolType <: Symbol.TermSymbol

  val symbol: SymbolType
  val accessor: BackendType
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
  accessor: BackendType,
  interface: Option[BackendType],
  hps: ListMap[Symbol.HardwareParamSymbol, HPElem],
  tps: ListMap[Symbol.TypeParamSymbol, BackendType]
) extends BackendLabel {
  override type SymbolType = Symbol.MethodSymbol

  override lazy val toString: String = {
    val interface = this.interface.map(_.toFirrtlString + "__").getOrElse("")
    val name = symbol.name
    val hargs = hps.values.map(_.toString)
    val targs = tps.values.map(_.toFirrtlString)
    val args = {
      val hargsStr =
        if(hargs.isEmpty) ""
        else "__" + hargs.mkString("_")

      val targsStr =
        if(targs.isEmpty) ""
        else "__" + targs.mkString("_")

      hargsStr + targsStr
    }

    interface + name + args
  }
}

case class StageLabel(
  symbol: Symbol.StageSymbol,
  accessor: BackendType,
  hps: ListMap[Symbol.HardwareParamSymbol, HPElem],
  tps: ListMap[Symbol.TypeParamSymbol, BackendType]
) extends BackendLabel {
  override type SymbolType = Symbol.StageSymbol
  override lazy val toString: String = symbol.name
}

case class StateLabel(
  symbol: Symbol.StateSymbol,
  accessor: BackendType,
  stage: String,
  hps: ListMap[Symbol.HardwareParamSymbol, HPElem],
  tps: ListMap[Symbol.TypeParamSymbol, BackendType]
) extends BackendLabel {
  override type SymbolType = Symbol.StateSymbol
  override lazy val toString: String = stage + "$" + symbol.name
}

case class AlwaysLabel(
  symbol: Symbol.AlwaysSymbol,
  accessor: BackendType,
  hps: ListMap[Symbol.HardwareParamSymbol, HPElem],
  tps: ListMap[Symbol.TypeParamSymbol, BackendType]
) extends BackendLabel {
  override type SymbolType = Symbol.AlwaysSymbol
  override lazy val toString: String = symbol.name
}

case class FieldLabel(
  symbol: Symbol.VariableSymbol,
  accessor: BackendType,
  hps: ListMap[Symbol.HardwareParamSymbol, HPElem],
  tps: ListMap[Symbol.TypeParamSymbol, BackendType]
) extends BackendLabel {
  override type SymbolType = Symbol.VariableSymbol
  override lazy val toString: String = symbol.name
}
