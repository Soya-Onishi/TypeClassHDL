package tchdl.util

import tchdl.backend._

import scala.collection.immutable.ListMap

trait BackendLabel

case class MethodLabel(symbol: Symbol.MethodSymbol, hps: ListMap[Symbol.HardwareParamSymbol, HPElem], tps: ListMap[Symbol.TypeParamSymbol, BackendType]) extends BackendLabel
case class StageLabel(symbol: Symbol.StageSymbol, hps: ListMap[Symbol.HardwareParamSymbol, HPElem], tps: ListMap[Symbol.TypeParamSymbol, BackendType]) extends BackendLabel
