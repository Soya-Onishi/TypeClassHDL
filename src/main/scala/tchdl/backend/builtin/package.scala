package tchdl.backend

import tchdl.backend.FirrtlCodeGen._
import tchdl.util.GlobalData

import firrtl.ir
import firrtl.PrimOps

package object builtin {
  def intAdd(left: Instance, right: Instance, global: GlobalData): Instance = {
    intBinOps(left, right, PrimOps.Add, global)(_ + _)
  }

  def intSub(left: Instance, right: Instance, global: GlobalData): Instance = {
    intBinOps(left, right, PrimOps.Sub, global)(_ - _)
  }

  def intMul(left: Instance, right: Instance, global: GlobalData): Instance = {
    intBinOps(left, right, PrimOps.Mul, global)(_ * _)
  }

  def intDiv(left: Instance, right: Instance, global: GlobalData): Instance = {
    intBinOps(left, right, PrimOps.Div, global)(_ / _)
  }

  def intEq(left: Instance, right: Instance, global: GlobalData): Instance = {
    intCmpOps(left, right, PrimOps.Eq, global)(_ == _)
  }

  def intNe(left: Instance, right: Instance, global: GlobalData): Instance = {
    intCmpOps(left, right, PrimOps.Neq, global)(_ != _)
  }

  def intGe(left: Instance, right: Instance, global: GlobalData): Instance = {
    intCmpOps(left, right, PrimOps.Geq, global)(_ >= _)
  }

  def intGt(left: Instance, right: Instance, global: GlobalData): Instance = {
    intCmpOps(left, right, PrimOps.Gt, global)(_ > _)
  }

  def intLe(left: Instance, right: Instance, global: GlobalData): Instance = {
    intCmpOps(left, right, PrimOps.Leq, global)(_ <= _)
  }

  def intLt(left: Instance, right: Instance, global: GlobalData): Instance = {
    intCmpOps(left, right, PrimOps.Lt, global)(_ < _)
  }

  def intNeg(operand: Instance, global: GlobalData): Instance = {
    intUnaryOps(operand, PrimOps.Neg, global)(value => -value)
  }

  def intNot(operand: Instance, global: GlobalData): Instance = {
    intUnaryOps(operand, PrimOps.Not, global)(value => ~value)
  }

  def boolEq(left: Instance, right: Instance, global: GlobalData): Instance = {
    boolBinOps(left, right, PrimOps.Eq, global)(_ == _)
  }

  def boolNe(left: Instance, right: Instance, global: GlobalData): Instance = {
    boolBinOps(left, right, PrimOps.Neq, global)(_ != _)
  }

  def boolNot(operand: Instance, global: GlobalData): Instance = {
    boolUnaryOps(operand, PrimOps.Not, global)(value => !value)
  }

  def bitAdd(left: Instance, right: Instance): Instance = {
    bitBinOps(left, right, PrimOps.Add)
  }

  def bitSub(left: Instance, right: Instance): Instance = {
    bitBinOps(left, right, PrimOps.Sub)
  }

  def bitMul(left: Instance, right: Instance): Instance = {
    bitBinOps(left, right, PrimOps.Mul)
  }

  def bitDiv(left: Instance, right: Instance): Instance = {
    bitBinOps(left, right, PrimOps.Div)
  }

  def bitEq(left: Instance, right: Instance): Instance = {
    bitBinOps(left, right, PrimOps.Eq)
  }

  def bitNe(left: Instance, right: Instance): Instance = {
    bitBinOps(left, right, PrimOps.Neq)
  }

  def bitGe(left: Instance, right: Instance): Instance = {
    bitBinOps(left, right, PrimOps.Geq)
  }

  def bitGt(left: Instance, right: Instance): Instance = {
    bitBinOps(left, right, PrimOps.Gt)
  }

  def bitLe(left: Instance, right: Instance): Instance = {
    bitBinOps(left, right, PrimOps.Leq)
  }

  def bitLt(left: Instance, right: Instance): Instance = {
    bitBinOps(left, right, PrimOps.Lt)
  }

  def bitNeg(operand: Instance): Instance = {
    bitUnaryOps(operand, PrimOps.Neg)
  }

  def bitNot(operand: Instance): Instance = {
    bitUnaryOps(operand, PrimOps.Not)
  }

  private def intBinOps(left: Instance, right: Instance, ops: ir.PrimOp, global: GlobalData)(f: (BigInt, BigInt) => BigInt): Instance = {
    val IntInstance(l) = left
    val IntInstance(r) = right

    val ret = (l, r) match {
      case (ir.UIntLiteral(left, _), ir.UIntLiteral(right, _)) => ir.UIntLiteral(f(left, right), ir.IntWidth(32))
      case (left, right) => ir.DoPrim(ops, Seq(left, right), Seq.empty, ir.UIntType(ir.IntWidth(32)))
    }

    IntInstance(ret)(global)
  }

  private def intCmpOps(left: Instance, right: Instance, ops: ir.PrimOp, global: GlobalData)(f: (BigInt, BigInt) => Boolean): Instance = {
    def toInt(bool: Boolean): BigInt =
      if(bool) BigInt(1)
      else     BigInt(0)

    val IntInstance(l) = left
    val IntInstance(r) = right

    val ret = (l, r) match {
      case (ir.UIntLiteral(left, _), ir.UIntLiteral(right, _)) => ir.UIntLiteral(toInt(f(left, right)), ir.IntWidth(1))
      case (left, right) => ir.DoPrim(ops, Seq(left, right), Seq.empty, ir.UIntType(ir.IntWidth(1)))
    }

    BoolInstance(ret)(global)
  }

  private def intUnaryOps(operand: Instance, ops: ir.PrimOp, global: GlobalData)(f: BigInt => BigInt): Instance = {
    val ret = operand match {
      case IntInstance(ir.UIntLiteral(value, _)) => ir.UIntLiteral(f(value), ir.IntWidth(32))
      case IntInstance(expr) => ir.DoPrim(ops, Seq(expr), Seq.empty, ir.UIntType(ir.IntWidth(32)))
    }

    IntInstance(ret)(global)
  }

  private def boolBinOps(left: Instance, right: Instance, ops: ir.PrimOp, global: GlobalData)(f: (Boolean, Boolean) => Boolean): Instance = {
    def toBool(lit: BigInt): Boolean = {
      lit.toInt match {
        case 0 => false
        case 1 => true
      }
    }

    def toRef(bool: Boolean): ir.UIntLiteral = {
      if(bool) ir.UIntLiteral(1, ir.IntWidth(1))
      else     ir.UIntLiteral(0, ir.IntWidth(1))
    }

    val BoolInstance(leftRef) = left
    val BoolInstance(rightRef) = right

    val retRef = (leftRef, rightRef) match {
      case (ir.UIntLiteral(left, _), ir.UIntLiteral(right, _)) =>
        val ret = f(toBool(left), toBool(right))
        toRef(ret)
      case (left, right) =>
        ir.DoPrim(ops, Seq(left, right), Seq.empty, ir.UIntType(ir.IntWidth(1)))
    }

    BoolInstance(retRef)(global)
  }

  private def boolUnaryOps(operand: Instance, ops: ir.PrimOp, global: GlobalData)(f: Boolean => Boolean): Instance = {
    def toBool(lit: BigInt): Boolean = {
      lit.toInt match {
        case 0 => false
        case 1 => true
      }
    }

    def toRef(bool: Boolean): ir.UIntLiteral = {
      if(bool) ir.UIntLiteral(1, ir.IntWidth(1))
      else     ir.UIntLiteral(0, ir.IntWidth(1))
    }

    val BoolInstance(ref) = operand

    val ret = ref match {
      case ir.UIntLiteral(value, _) => (toRef _ compose f compose toBool)(value)
      case expr => ir.DoPrim(ops, Seq(expr), Seq.empty, ir.UIntType(ir.IntWidth(1)))
    }

    BoolInstance(ret)(global)
  }

  private def bitBinOps(left: Instance, right: Instance, ops: ir.PrimOp): Instance = {
    val BitInstance(tpe, leftRef) = left
    val BitInstance(_, rightRef) = right

    BitInstance(tpe, ir.DoPrim(ops, Seq(leftRef, rightRef), Seq.empty, ir.UnknownType))
  }

  private def bitUnaryOps(operand: Instance, ops: ir.PrimOp): Instance = {
    val BitInstance(tpe, ref) = operand

    BitInstance(tpe, ir.DoPrim(ops, Seq(ref), Seq.empty, ir.UnknownType))
  }
}
