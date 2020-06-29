package tchdl.util

import tchdl.backend._

abstract class BackendContext[T <: BackendLabel]() {
  val temp: TempCounter = new TempCounter

  val label: T
  val hpTable: Map[Symbol.HardwareParamSymbol, HPElem]
  val tpTable: Map[Symbol.TypeParamSymbol, BackendType]

  def copy(_label: T): BackendContext[T] = {
    val oldTemp = this.temp

    new BackendContext[T] {
      override val temp = oldTemp

      override val label = _label
      override val hpTable = _label.hps
      override val tpTable = _label.tps
    }
  }
}

object BackendContext {
  def apply[T <: BackendLabel](_label: T): BackendContext[T] = {
    new BackendContext[T] {
      override val label = _label
      override val hpTable = _label.hps
      override val tpTable = _label.tps
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
