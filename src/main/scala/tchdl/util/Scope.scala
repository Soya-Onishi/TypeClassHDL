package tchdl.util

import scala.collection.mutable

class Scope[T](parent: Option[Scope[T]]) {
  private val scope = mutable.HashMap[String, T]()

  def append(name: String, elem: T): Either[Error, Unit] = {
    if(scope.contains(name)) Left(???)
    else {
      scope(name) = elem
      Right(())
    }
  }

  def lookup(name: String): Either[Error, T] = {
    scope.get(name) match {
      case Some(elem) => Right(elem)
      case None => parent match {
        case Some(p) => p.lookup(name)
        case None => Left(???)
      }
    }
  }
}
