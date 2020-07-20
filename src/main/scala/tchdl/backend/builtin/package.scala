package tchdl.backend

import tchdl.util.Type
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

  def bitEq(left: Instance, right: Instance, global: GlobalData): Instance = {
    bitCmpOps(left, right, PrimOps.Eq, global)
  }

  def bitNe(left: Instance, right: Instance, global: GlobalData): Instance = {
    bitCmpOps(left, right, PrimOps.Neq, global)
  }

  def bitGe(left: Instance, right: Instance, global: GlobalData): Instance = {
    bitCmpOps(left, right, PrimOps.Geq, global)
  }

  def bitGt(left: Instance, right: Instance, global: GlobalData): Instance = {
    bitCmpOps(left, right, PrimOps.Gt, global)
  }

  def bitLe(left: Instance, right: Instance, global: GlobalData): Instance = {
    bitCmpOps(left, right, PrimOps.Leq, global)
  }

  def bitLt(left: Instance, right: Instance, global: GlobalData): Instance = {
    bitCmpOps(left, right, PrimOps.Lt, global)
  }

  def bitNeg(operand: Instance): Instance = {
    bitUnaryOps(operand, PrimOps.Neg)
  }

  def bitNot(operand: Instance): Instance = {
    bitUnaryOps(operand, PrimOps.Not)
  }

  def bitTruncate(operand: Instance, hi: HPElem, lo: HPElem, global: GlobalData): Instance = {
    val HPElem.Num(hiIndex) = hi
    val HPElem.Num(loIndex) = lo
    val DataInstance(_, refer) = operand
    val truncate = ir.DoPrim(PrimOps.Bits, Seq(refer), Seq(hiIndex, loIndex), ir.UnknownType)

    val width = hiIndex - loIndex + 1
    val retTpe = toBackendType(Type.bitTpe(width)(global))(global)

    DataInstance(retTpe, truncate)
  }

  def bitBit(operand: Instance, index: HPElem, global: GlobalData): Instance = {
    val HPElem.Num(idx) = index
    val DataInstance(_, refer) = operand
    val bit = ir.DoPrim(PrimOps.Bits, Seq(refer), Seq(idx, idx), ir.UnknownType)
    val retTpe = toBackendType(Type.bitTpe(1)(global))(global)

    DataInstance(retTpe, bit)
  }

  def bitConcat(left: Instance, right: Instance, global: GlobalData): Instance = {
    val DataInstance(BackendType(_, leftHargs, _), l) = left
    val DataInstance(BackendType(_, rightHargs, _), r) = right
    val concat = ir.DoPrim(PrimOps.Cat, Seq(l, r), Seq.empty, ir.UnknownType)

    val HPElem.Num(leftWidth) = leftHargs.head
    val HPElem.Num(rightWidth) = rightHargs.head
    val width = leftWidth + rightWidth
    val retTpe = toBackendType(Type.bitTpe(width)(global))(global)

    DataInstance(retTpe, concat)
  }

  private def intBinOps(left: Instance, right: Instance, ops: ir.PrimOp, global: GlobalData)(f: (BigInt, BigInt) => BigInt): Instance = {
    val DataInstance(tpe, l) = left
    val DataInstance(_, r) = right

    val ret = (l, r) match {
      case (ir.UIntLiteral(left, _), ir.UIntLiteral(right, _)) => ir.UIntLiteral(f(left, right), ir.IntWidth(32))
      case (left, right) => ir.DoPrim(ops, Seq(left, right), Seq.empty, ir.UIntType(ir.IntWidth(32)))
    }

    DataInstance(tpe, ret)
  }

  private def intCmpOps(left: Instance, right: Instance, ops: ir.PrimOp, global: GlobalData)(f: (BigInt, BigInt) => Boolean): Instance = {
    def toInt(bool: Boolean): BigInt =
      if(bool) BigInt(1)
      else     BigInt(0)

    val DataInstance(_, l) = left
    val DataInstance(_, r) = right

    val ret = (l, r) match {
      case (ir.UIntLiteral(left, _), ir.UIntLiteral(right, _)) => ir.UIntLiteral(toInt(f(left, right)), ir.IntWidth(1))
      case (left, right) => ir.DoPrim(ops, Seq(left, right), Seq.empty, ir.UIntType(ir.IntWidth(1)))
    }

    val boolTpe = toBackendType(Type.boolTpe(global))(global)
    DataInstance(boolTpe, ret)
  }

  private def intUnaryOps(operand: Instance, ops: ir.PrimOp, global: GlobalData)(f: BigInt => BigInt): Instance = {
    val ret = operand match {
      case DataInstance(_, ir.UIntLiteral(value, _)) => ir.UIntLiteral(f(value), ir.IntWidth(32))
      case DataInstance(_, expr) => ir.DoPrim(ops, Seq(expr), Seq.empty, ir.UIntType(ir.IntWidth(32)))
    }

    DataInstance(operand.tpe, ret)
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

    val DataInstance(tpe, leftRef) = left
    val DataInstance(_, rightRef) = right

    val retRef = (leftRef, rightRef) match {
      case (ir.UIntLiteral(left, _), ir.UIntLiteral(right, _)) =>
        val ret = f(toBool(left), toBool(right))
        toRef(ret)
      case (left, right) =>
        ir.DoPrim(ops, Seq(left, right), Seq.empty, ir.UIntType(ir.IntWidth(1)))
    }

    DataInstance(tpe, retRef)
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

    val DataInstance(_, ref) = operand

    val ret = ref match {
      case ir.UIntLiteral(value, _) => (toRef _ compose f compose toBool)(value)
      case expr => ir.DoPrim(ops, Seq(expr), Seq.empty, ir.UIntType(ir.IntWidth(1)))
    }

    DataInstance(operand.tpe, ret)
  }

  private def bitBinOps(left: Instance, right: Instance, ops: ir.PrimOp): Instance = {
    val DataInstance(tpe, leftRef) = left
    val DataInstance(_, rightRef) = right

    DataInstance(tpe, ir.DoPrim(ops, Seq(leftRef, rightRef), Seq.empty, ir.UnknownType))
  }

  private def bitCmpOps(left: Instance, right: Instance, ops: ir.PrimOp, global: GlobalData): Instance = {
    val DataInstance(_, leftRef) = left
    val DataInstance(_, rightRef) = right

    val retTpe = toBackendType(Type.bitTpe(1)(global))(global)

    DataInstance(retTpe, ir.DoPrim(ops, Seq(leftRef, rightRef), Seq.empty, ir.UnknownType))
  }

  private def bitUnaryOps(operand: Instance, ops: ir.PrimOp): Instance = {
    val DataInstance(tpe, ref) = operand

    DataInstance(tpe, ir.DoPrim(ops, Seq(ref), Seq.empty, ir.UnknownType))
  }
}
