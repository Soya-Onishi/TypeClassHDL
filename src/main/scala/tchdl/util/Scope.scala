package tchdl.util

import scala.collection.mutable

class Scope {
  private val table = mutable.HashMap[String, Symbol]()

  def append(symbol: Symbol): Either[Error, Unit] = {
    if (table.contains(symbol.name)) Left(???)
    else {
      table(symbol.name) = symbol
      Right(())
    }
  }

  def lookup(name: String): Option[Symbol] = {
    table.get(name)
  }
}

object Scope {
  def empty = new Scope
}