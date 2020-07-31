package tchdl.util

import tchdl.ast.Position

import scala.collection.mutable

class Scope {
  private val table = mutable.HashMap[String, Symbol]()

  def append(symbol: Symbol): Either[Error, Unit] = {
    if (table.contains(symbol.name))
      Left(Error.DefinitionNameConflict(symbol.name, Position.empty))
    else {
      table(symbol.name) = symbol
      Right(())
    }
  }

  def lookup(name: String): Option[Symbol] = {
    table.get(name)
  }

  def toMap: Map[String, Symbol] = table.toMap
}

object Scope {
  def empty = new Scope
}