package tchdl.util

import tchdl.ast._

case class Constraint(target: Expression with HPExpr, range: HPRange)

case class HPRange(
  min: RangeEdge,
  max: RangeEdge
) {
  /*
  def isOverlap(that: Range): Boolean = {
    def maxOverlap = this.max.isEmpty && that.max.isEmpty
    def minOverlap = this.min.isEmpty && that.min.isEmpty
    def overlap(r0: Range, r1: Range): Boolean = {
      def verifyMinMax: Boolean = (r0.min, r1.max) match {
        case (None, _) => true
        case (_, None) => true
        case (Some(min), Some(max)) => min <= max
      }

      def verifyMaxMin: Boolean = (r0.max, r1.min) match {
        case (None, _) => true
        case (_, None) => true
        case (Some(max), Some(min)) => max >= min
      }
    }

    maxOverlap || minOverlap || overlap(this, that) || overlap(that, this)
  }
  */

  def unify(that: HPRange): Either[Error, HPRange] = {
    if(this.min.nonInf && that.min.nonInf) Left(???) // TODO: Add error that represents min is already assigned
    else if(this.max.nonInf && that.max.nonInf) Left(???)
    else {
      val min =
        if(this.min.nonInf) this.min
        else that.min

      val max =
        if(this.max.nonInf) this.max
        else that.max

      Right(HPRange(min, max))
    }
  }

  def isConstant: Boolean = {
    (this.min, this.max) match {
      case (RangeEdge.ThanEq(left: IntLiteral), RangeEdge.ThanEq(right: IntLiteral)) => left == right
      case _ => false
    }
  }
}

trait RangeEdge {
  def isInf: Boolean = this.isInstanceOf[RangeEdge.Inf.type]
  def nonInf: Boolean = !isInf
}
object RangeEdge {
  case object Inf extends RangeEdge
  case class ThanEq(expr: Expression with ConstraintTarget) extends RangeEdge
  case class Than(expr: Expression with ConstraintTarget) extends RangeEdge
}