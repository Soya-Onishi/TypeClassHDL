package tchdl.util

import tchdl.backend._
import tchdl.util.TchdlException.ImplementationErrorException

import scala.collection.mutable
import scala.collection.immutable.ListMap

abstract class BackendContext {
  val temp: TempCounter = new TempCounter
  private val scope: mutable.Map[Symbol.TermSymbol, String] = mutable.Map.empty
  val parent: Option[BackendContext]

  val label: BackendLabel
  val tpBound: Map[Type.RefType, Vector[BackendType]]

  def append(symbol: Symbol.TermSymbol, name: String): Unit = scope(symbol) = name
  def lookup(symbol: Symbol.TermSymbol): String = scope.get(symbol) match {
    case Some(name) => name
    case None if parent.isEmpty => throw new ImplementationErrorException("symbol must be found")
    case None => parent.get.lookup(symbol)
  }

  def hpTable: ListMap[Symbol.HardwareParamSymbol, HPElem] = label.hps
  def tpTable: ListMap[Symbol.TypeParamSymbol, BackendType] = label.tps
}

object BackendContext {
  def apply(label: BackendLabel, tpBound: Map[Type.RefType, Vector[BackendType]]): BackendContext = {
    val _label = label
    val _tpBound = tpBound

    new BackendContext {
      override val parent: Option[BackendContext] = None

      override val label = _label
      override val tpBound = _tpBound
    }
  }

  def apply(parent: BackendContext, label: BackendLabel): BackendContext = {
    val _label = label
    val _parent = parent

    new BackendContext {
      override val parent: Option[BackendContext] = Some(_parent)

      override val label = _label
      override val tpBound = _parent.tpBound
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
