package tchdl.util

import tchdl.ast._

trait IInt {
  override def equals(obj: Any): Boolean = obj match {
    case that: IInt => (this, that) match {
      case (IInt.Inf(s0, e0), IInt.Inf(s1, e1)) => s0 == s1 && e0 == e1
      case (IInt.Integer(v0), IInt.Integer(v1)) => v0 == v1
      case _ => false
    }
    case _ => false
  }


  def >(that: IInt): Boolean = comp(that) > 0
  def >=(that: IInt): Boolean = comp(that) >= 0
  def <(that: IInt): Boolean = comp(that) < 0
  def <=(that: IInt): Boolean = comp(that) <= 0
  private def comp(that: IInt): Int = {
    (this, that) match {
      case (IInt.Inf(Sign.Pos, _), IInt.Inf(Sign.Pos, _)) => 0
      case (IInt.Inf(Sign.Pos, _), IInt.Inf(Sign.Neg, _)) => 1
      case (IInt.Inf(Sign.Neg, _), IInt.Inf(Sign.Pos, _)) => -1
      case (IInt.Inf(Sign.Neg, _), IInt.Inf(Sign.Neg, _)) => 0
      case (IInt.Inf(Sign.Pos, _), _) =>  1
      case (IInt.Inf(Sign.Neg, _), _) => -1
      case (_, IInt.Inf(Sign.Pos, _)) => -1
      case (_, IInt.Inf(Sign.Neg, _)) =>  1
      case (IInt.Integer(v0), IInt.Integer(v1)) =>
        if(v0 > v1)        1
        else if(v0 == v1)  0
        else              -1
    }
  }

  override def hashCode: Int =
    this match {
      case IInt.Inf(sign, expr) => IInt.Inf.getClass.hashCode + sign.hashCode + expr.hashCode
      case IInt.Integer(value)  => value.hashCode
    }

  def isInf: Boolean = this.isInstanceOf[IInt.Inf]
}


object IInt {
  case class Inf(sign: Sign, expr: HPExpr) extends IInt
  case class Integer(value: Int) extends IInt

  def apply(num: Int): IInt = IInt.Integer(num)
  def nInf(expr: HPExpr): IInt = IInt.Inf(Sign.Neg, expr)
  def pInf(expr: HPExpr): IInt = IInt.Inf(Sign.Pos, expr)
}

trait Sign
object Sign {
  case object Pos extends Sign
  case object Neg extends Sign
}
