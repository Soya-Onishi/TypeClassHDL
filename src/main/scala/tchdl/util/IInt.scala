package tchdl.util

trait IInt extends Ordered[IInt] {
  def +(other: IInt): IInt =
    (this, other) match {
      case (IInt.PInf, _) => IInt.PInf
      case (IInt.NInf, _) => IInt.NInf
      case (_, IInt.PInf) => IInt.PInf
      case (_, IInt.NInf) => IInt.NInf
      case (IInt.Integer(v0), IInt.Integer(v1)) => IInt.Integer(v0 + v1)
    }

  def -(other: IInt): IInt =
    this + (-other)

  def *(other: IInt): IInt =
    (this, other) match {
      case (IInt.PInf, IInt.NInf) => IInt.NInf
      case (IInt.NInf, IInt.PInf) => IInt.NInf
      case (IInt.PInf, IInt.PInf) => IInt.PInf
      case (IInt.NInf, IInt.NInf) => IInt.NInf
      case (IInt.PInf, IInt.Integer(0)) => IInt.Integer(0)
      case (IInt.PInf, IInt.Integer(v)) if v > 0 => IInt.PInf
      case (IInt.PInf, IInt.Integer(v)) if v < 0 => IInt.NInf
      case (IInt.NInf, IInt.Integer(0)) => IInt.Integer(0)
      case (IInt.NInf, IInt.Integer(v)) if v > 0 => IInt.NInf
      case (IInt.NInf, IInt.Integer(v)) if v < 0 => IInt.PInf
      case (IInt.Integer(0), IInt.PInf) => IInt.Integer(0)
      case (IInt.Integer(v), IInt.PInf) if v > 0 => IInt.PInf
      case (IInt.Integer(v), IInt.PInf) if v < 0 => IInt.NInf
      case (IInt.Integer(0), IInt.NInf) => IInt.Integer(0)
      case (IInt.Integer(v), IInt.NInf) if v > 0 => IInt.NInf
      case (IInt.Integer(v), IInt.NInf) if v < 0 => IInt.PInf
      case (IInt.Integer(v0), IInt.Integer(v1)) => IInt.Integer(v0 * v1)
    }

  def /(other: IInt): IInt =
    (this, other) match {
      case (IInt.PInf, IInt.NInf) => IInt.NInf
      case (IInt.NInf, IInt.PInf) => IInt.NInf
      case (IInt.PInf, IInt.PInf) => IInt.PInf
      case (IInt.NInf, IInt.NInf) => IInt.NInf
      case (IInt.PInf, IInt.Integer(0)) => IInt.PInf
      case (IInt.PInf, IInt.Integer(v)) if v > 0 => IInt.PInf
      case (IInt.PInf, IInt.Integer(v)) if v < 0 => IInt.NInf
      case (IInt.NInf, IInt.Integer(0)) => IInt.NInf
      case (IInt.NInf, IInt.Integer(v)) if v > 0 => IInt.NInf
      case (IInt.NInf, IInt.Integer(v)) if v < 0 => IInt.PInf
      case (IInt.Integer(_), IInt.PInf) => IInt.Integer(0)
      case (IInt.Integer(_), IInt.NInf) => IInt.Integer(0)
      case (IInt.Integer(v), IInt.Integer(0)) if v >= 0 => IInt.PInf
      case (IInt.Integer(v), IInt.Integer(0)) if v < 0 => IInt.NInf
      case (IInt.Integer(v0), IInt.Integer(v1)) => IInt.Integer(v0 / v1)
    }

  def unary_- : IInt = this match {
    case IInt.PInf => IInt.NInf
    case IInt.NInf => IInt.PInf
    case IInt.Integer(v) => IInt.Integer(-v)
  }

  override def equals(obj: Any): Boolean = obj match {
    case that: IInt => (this, that) match {
      case (IInt.PInf, IInt.PInf) => true
      case (IInt.NInf, IInt.NInf) => true
      case (IInt.Integer(v0), IInt.Integer(v1)) => v0 == v1
      case _ => false
    }
    case _ => false
  }

  override def compare(that: IInt): Int = (this, that) match {
    case (IInt.PInf, _) => 1
    case (IInt.NInf, _) => -1
    case (IInt.Integer(v0), IInt.Integer(v1)) =>
      if(v0 == v1) 0
      else if(v0 < v1) -1
      else 1
  }

  def isPInf: Boolean = this.isInstanceOf[IInt.PInf.type]
  def isNInf: Boolean = this.isInstanceOf[IInt.NInf.type]
}


object IInt {
  case object NInf extends IInt
  case object PInf extends IInt
  case class Integer(value: Int) extends IInt

  def apply(num: Int): IInt = IInt.Integer(num)
  def nInf: IInt = IInt.NInf
  def pInf: IInt = IInt.PInf
}
