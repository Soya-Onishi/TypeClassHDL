package tchdl.util

import scala.annotation.tailrec
import scala.collection.mutable

class Scope(parent: Option[Scope]) {
  private val tpetab = mutable.HashMap[String, Type]()
  private val symtab = mutable.HashMap[String, Symbol]()

  def appendSym(symbol: Symbol): Either[Error, Unit] = {
    append(symbol.name, symbol, symtab)
  }

  def lookupSym(name: String): Either[Error, Symbol] = {
    lookup(name, symtab)
  }

  def appendType(tpe: Type): Either[Error, Unit] = {
    append(tpe.name, tpe, tpetab)
  }

  def lookupType(name: String): Either[Error, Type] = {
    lookup(name, tpetab)
  }

  private def append[T](name: String, sym: T, table: mutable.HashMap[String, T]): Either[Error, Unit] = {
    if(table.contains(name)) Left(???)
    else {
      table(name) = sym
      Right(())
    }
  }

  @tailrec
  private def lookup[T](name: String, table: mutable.HashMap[String, T]): Either[Error, T] = {
    table.get(name) match {
      case Some(elem) => Right(elem)
      case None => parent match {
        case Some(p) => p.lookup(name, table)
        case None => Left(???)
      }
    }
  }
}

object Scope {
  def apply(parent: Scope): Scope = {
    new Scope(Some(parent))
  }

  def root(): Scope = {
    new Scope(None)
  }
}
