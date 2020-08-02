package tchdl.backend

import firrtl.ir

case class Future(froms: Map[ir.Expression, Vector[ir.Expression]], futures: Map[ir.Expression, UsageStyle]) {
  def + (that: Future): Future = {
    val newAccesses = that.froms.foldLeft(this.froms) {
      case (accesses, (loc, froms)) => accesses.get(loc) match {
        case None => accesses.updated(loc, froms)
        case Some(thisFroms) => accesses.updated(loc, froms ++ thisFroms)
      }
    }

    Future(newAccesses, this.futures ++ that.futures)
  }
}

object Future {
  def empty: Future = Future(Map.empty[ir.Expression, Vector[ir.Expression]], Map.empty[ir.Expression, UsageStyle])
}

trait UsageStyle
object UsageStyle {
  case class Local(tpe: ir.Type) extends UsageStyle
  case object Field extends UsageStyle
  case class Constructor(tpe: ir.Type) extends UsageStyle
}

trait Direction
object Direction {
  case object Input extends Direction
  case object Output extends Direction
  case object Internal extends Direction
}