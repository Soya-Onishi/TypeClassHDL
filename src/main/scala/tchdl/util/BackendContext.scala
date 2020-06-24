package tchdl.util

import tchdl.backend._

abstract class BackendContext() {
  import scala.collection.mutable

  val temp: TempNamer = new TempNamer
  val methodTable: mutable.Map[MethodLabel, Option[MethodContainer]] = mutable.Map()
  val interfaceTable: mutable.Map[BackendType, MethodLabel] = mutable.Map()

  val hpTable: Map[Symbol.HardwareParamSymbol, HPElem]
  val tpTable: Map[Symbol.TypeParamSymbol, BackendType]
  val hpBounds: Vector[HPBound]
  val tpBounds: Vector[TPBound]

  def copy(
    _hpTable: Map[Symbol.HardwareParamSymbol, HPElem],
    _tpTable: Map[Symbol.TypeParamSymbol, BackendType],
    _hpBounds: Vector[HPBound],
    _tpBounds: Vector[TPBound]
  ): BackendContext = {
    val oldTemp = this.temp
    val oldMethodTable = this.methodTable
    val oldInterfaceTable = this.interfaceTable

    new BackendContext {
      override val temp = oldTemp
      override val methodTable = oldMethodTable
      override val interfaceTable = oldInterfaceTable

      override val hpTable = _hpTable
      override val tpTable = _tpTable
      override val hpBounds = _hpBounds
      override val tpBounds = _tpBounds
    }
  }
}

object BackendContext {
  def apply(
    _hpTable: Map[Symbol.HardwareParamSymbol, HPElem],
    _tpTable: Map[Symbol.TypeParamSymbol, BackendType],
    _hpBounds: Vector[HPBound],
    _tpBounds: Vector[TPBound]
  ): BackendContext = {
    new BackendContext {
      override val hpTable = _hpTable
      override val tpTable = _tpTable
      override val hpBounds = _hpBounds
      override val tpBounds = _tpBounds
    }
  }
}

class TempNamer {
  private var _id: Int = 0

  def get(): String = {
    val id = _id
    _id = _id + 1

    s"TEMP_$id"
  }
}
