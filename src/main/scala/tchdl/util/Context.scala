package tchdl.util

import scala.collection.mutable

case class Context(
  parent: Option[Context],
  owner: Option[Symbol],
  namespace: Vector[String],
) {
  val declares = mutable.Map[String, Seq[Symbol]]()

  def enter(name: String, symbol: Symbol): Unit = declares.get(name) match {
    case None => declares(name) = Seq(symbol)
    case Some(symbols) => declares(name) = symbols :+ symbol
  }

  def lookup(name: String): LookupResult = declares.get(name) match {
    case Some(seq) => LookupResult.LookupSuccess(seq)
    case None => parent match {
      case Some(parent) => parent.lookup(name)
      case None => LookupResult.LookupFailure(name)
    }
  }
}

trait LookupResult
object LookupResult {
  case class LookupSuccess(symbols: Seq[Symbol]) extends LookupResult
  case class LookupFailure(name: String) extends LookupResult
}


