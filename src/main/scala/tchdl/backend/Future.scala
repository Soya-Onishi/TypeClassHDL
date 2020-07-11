package tchdl.backend

import firrtl.ir

case class Future(accesses: Map[ir.Expression, Vector[ir.Expression]], futures: Map[ir.Expression, FormKind]) {
  def + (that: Future): Future = {
    val newAccesses = that.accesses.foldLeft(this.accesses) {
      case (accesses, (loc, froms)) => accesses.get(loc) match {
        case None => accesses.updated(loc, froms)
        case Some(thisFroms) => accesses.updated(loc, froms ++ thisFroms)
      }
    }

    Future(newAccesses, this.futures ++ that.futures)
  }
}

object Future {
  def empty: Future = Future(Map.empty[ir.Expression, Vector[ir.Expression]], Map.empty[ir.Expression, FormKind])
}

trait FormKind
object FormKind {
  case class Local(froms: Vector[ir.Expression], tpe: ir.Type) extends FormKind
  case object Field extends FormKind
  case object Stage extends FormKind
  case class Constructor(tpe: ir.Type) extends FormKind
}

trait Direction
object Direction {
  case object Input extends Direction
  case object Output extends Direction
  case object Internal extends Direction
}