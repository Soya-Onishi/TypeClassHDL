package tchdl.backend

import tchdl.util.Type
import tchdl.util.GlobalData
import firrtl.ir
import firrtl.PrimOps
import tchdl.backend.FirrtlCodeGen.StackFrame

package object builtin {
  def intAdd(left: Instance, right: Instance, global: GlobalData): RunResult = {
    intBinOps(left, right, PrimOps.Add, global)(_ + _)
  }

  def intSub(left: Instance, right: Instance, global: GlobalData): RunResult = {
    intBinOps(left, right, PrimOps.Sub, global)(_ - _)
  }

  def intMul(left: Instance, right: Instance, global: GlobalData): RunResult = {
    intBinOps(left, right, PrimOps.Mul, global)(_ * _)
  }

  def intDiv(left: Instance, right: Instance, global: GlobalData): RunResult = {
    intBinOps(left, right, PrimOps.Div, global)(_ / _)
  }

  def intEq(left: Instance, right: Instance, global: GlobalData): RunResult = {
    intCmpOps(left, right, PrimOps.Eq, global)(_ == _)
  }

  def intNe(left: Instance, right: Instance, global: GlobalData): RunResult = {
    intCmpOps(left, right, PrimOps.Neq, global)(_ != _)
  }

  def intGe(left: Instance, right: Instance, global: GlobalData): RunResult = {
    intCmpOps(left, right, PrimOps.Geq, global)(_ >= _)
  }

  def intGt(left: Instance, right: Instance, global: GlobalData): RunResult = {
    intCmpOps(left, right, PrimOps.Gt, global)(_ > _)
  }

  def intLe(left: Instance, right: Instance, global: GlobalData): RunResult = {
    intCmpOps(left, right, PrimOps.Leq, global)(_ <= _)
  }

  def intLt(left: Instance, right: Instance, global: GlobalData): RunResult = {
    intCmpOps(left, right, PrimOps.Lt, global)(_ < _)
  }

  def intNeg(operand: Instance, global: GlobalData): RunResult = {
    intUnaryOps(operand, PrimOps.Neg, global)(value => -value)
  }

  def intNot(operand: Instance, global: GlobalData): RunResult = {
    intUnaryOps(operand, PrimOps.Not, global)(value => ~value)
  }

  def boolEq(left: Instance, right: Instance, global: GlobalData): RunResult = {
    boolBinOps(left, right, PrimOps.Eq, global)(_ == _)
  }

  def boolNe(left: Instance, right: Instance, global: GlobalData): RunResult = {
    boolBinOps(left, right, PrimOps.Neq, global)(_ != _)
  }

  def boolNot(operand: Instance, global: GlobalData): RunResult = {
    boolUnaryOps(operand, PrimOps.Not, global)(value => !value)
  }

  def bitAdd(left: Instance, right: Instance): RunResult = {
    bitBinOps(left, right, PrimOps.Add)
  }

  def bitSub(left: Instance, right: Instance): RunResult = {
    bitBinOps(left, right, PrimOps.Sub)
  }

  def bitMul(left: Instance, right: Instance): RunResult = {
    bitBinOps(left, right, PrimOps.Mul)
  }

  def bitDiv(left: Instance, right: Instance): RunResult = {
    bitBinOps(left, right, PrimOps.Div)
  }

  def bitEq(left: Instance, right: Instance, global: GlobalData): RunResult = {
    bitCmpOps(left, right, PrimOps.Eq, global)
  }

  def bitNe(left: Instance, right: Instance, global: GlobalData): RunResult = {
    bitCmpOps(left, right, PrimOps.Neq, global)
  }

  def bitGe(left: Instance, right: Instance, global: GlobalData): RunResult = {
    bitCmpOps(left, right, PrimOps.Geq, global)
  }

  def bitGt(left: Instance, right: Instance, global: GlobalData): RunResult = {
    bitCmpOps(left, right, PrimOps.Gt, global)
  }

  def bitLe(left: Instance, right: Instance, global: GlobalData): RunResult = {
    bitCmpOps(left, right, PrimOps.Leq, global)
  }

  def bitLt(left: Instance, right: Instance, global: GlobalData): RunResult = {
    bitCmpOps(left, right, PrimOps.Lt, global)
  }

  def bitNeg(operand: Instance): RunResult = {
    bitUnaryOps(operand, PrimOps.Neg)
  }

  def bitNot(operand: Instance): RunResult = {
    bitUnaryOps(operand, PrimOps.Not)
  }

  def bitTruncate(operand: Instance, hi: HPElem, lo: HPElem, global: GlobalData): RunResult = {
    val HPElem.Num(hiIndex) = hi
    val HPElem.Num(loIndex) = lo
    val DataInstance(_, refer) = operand
    val truncate = ir.DoPrim(PrimOps.Bits, Seq(refer), Seq(hiIndex, loIndex), ir.UnknownType)

    val width = hiIndex - loIndex + 1
    val retTpe = toBackendType(Type.bitTpe(width)(global))(global)

    RunResult.inst(DataInstance(retTpe, truncate))
  }

  def bitBit(operand: Instance, index: HPElem, global: GlobalData): RunResult = {
    val HPElem.Num(idx) = index
    val DataInstance(_, refer) = operand
    val bit = ir.DoPrim(PrimOps.Bits, Seq(refer), Seq(idx, idx), ir.UnknownType)
    val retTpe = toBackendType(Type.bitTpe(1)(global))(global)

    RunResult.inst(DataInstance(retTpe, bit))
  }

  def bitConcat(left: Instance, right: Instance, global: GlobalData): RunResult = {
    val DataInstance(BackendType(_, leftHargs, _), l) = left
    val DataInstance(BackendType(_, rightHargs, _), r) = right
    val concat = ir.DoPrim(PrimOps.Cat, Seq(l, r), Seq.empty, ir.UnknownType)

    val HPElem.Num(leftWidth) = leftHargs.head
    val HPElem.Num(rightWidth) = rightHargs.head
    val width = leftWidth + rightWidth
    val retTpe = toBackendType(Type.bitTpe(width)(global))(global)

    RunResult.inst(DataInstance(retTpe, concat))
  }

  def vecIdx(accessor: Instance, index: HPElem, global: GlobalData): RunResult = {
    val HPElem.Num(idx) = index
    val DataInstance(tpe, refer) = accessor
    val elemType = tpe.targs.head
    val subIndex = ir.SubIndex(refer, idx, toFirrtlType(elemType)(global))

    RunResult.inst(DataInstance(elemType, subIndex))
  }

  def vecIdxDyn(accessor: Instance, index: Instance, global: GlobalData): RunResult = {
    val DataInstance(_, idx) = index
    val DataInstance(tpe, refer) = accessor
    val elemType = tpe.targs.head
    val subAccess = ir.SubAccess(refer, idx, toFirrtlType(elemType)(global))

    RunResult.inst(DataInstance(elemType, subAccess))
  }

  def vecUpdated(accessor: Instance, elem: Instance, index: HPElem)(implicit stack: StackFrame, global: GlobalData): RunResult = {
    val name = stack.next("_VEC_UPDATED")
    val vecTpe = toFirrtlType(accessor.tpe)

    val DataInstance(_, vecRef) = accessor
    val DataInstance(_, elemRef) = elem
    val HPElem.Num(idx) = index

    val wire = ir.DefWire(ir.NoInfo, name.name, vecTpe)
    val wireRef = ir.Reference(wire.name, vecTpe)
    val init = ir.Connect(ir.NoInfo, wireRef, vecRef)
    val update = ir.Connect(
      ir.NoInfo,
      ir.SubIndex(wireRef, idx, ir.UnknownType),
      elemRef
    )

    val stmts = Vector(wire, init, update)
    val instance = DataInstance(accessor.tpe, wireRef)

    RunResult(Future.empty, stmts, instance)
  }

  def vecUpdatedDyn(accessor: Instance, index: Instance, elem: Instance)(implicit stack: StackFrame, global: GlobalData): RunResult = {
    val name = stack.next("_VEC_UPDATED")
    val vecTpe = toFirrtlType(accessor.tpe)

    val DataInstance(_, vecRef) = accessor
    val DataInstance(_, elemRef) = elem
    val DataInstance(_, idxRef) = index

    val wire = ir.DefWire(ir.NoInfo, name.name, vecTpe)
    val wireRef = ir.Reference(wire.name, vecTpe)
    val init = ir.Connect(ir.NoInfo, wireRef, vecRef)
    val update = ir.Connect(
      ir.NoInfo,
      ir.SubAccess(wireRef, idxRef, ir.UnknownType),
      elemRef
    )

    val stmts = Vector(wire, init, update)
    val instance = DataInstance(accessor.tpe, wireRef)

    RunResult(Future.empty, stmts, instance)
  }

  def bitFromInt(bitTpe: BackendType, from: Instance)(implicit global: GlobalData): RunResult = {
    val HPElem.Num(toWidth) = bitTpe.hargs.head
    val DataInstance(_, refer) = from
    val casted =
      if(toWidth > 32) ir.DoPrim(PrimOps.Pad, Seq(refer), Seq(toWidth - 32), ir.UnknownType)
      else ir.DoPrim(PrimOps.Bits, Seq(refer), Seq(toWidth - 1, 0), ir.UnknownType)

    val retTpe = toBackendType(Type.bitTpe(toWidth))
    val retInstance = DataInstance(retTpe, casted)

    RunResult(Future.empty, Vector.empty, retInstance)
  }

  def bitFromBool(bitTpe: BackendType, from: Instance)(implicit global: GlobalData): RunResult = {
    val HPElem.Num(toWidth) = bitTpe.hargs.head
    val DataInstance(_, refer) = from
    val casted = ir.DoPrim(PrimOps.Pad, Seq(refer), Seq(toWidth - 1), ir.UnknownType)
    val retTpe = toBackendType(Type.bitTpe(toWidth))
    val retInstance = DataInstance(retTpe, casted)

    RunResult(Future.empty, Vector.empty, retInstance)
  }

  def bitFromBit(bitTpe: BackendType, from: Instance)(implicit global: GlobalData): RunResult = {
    val HPElem.Num(toWidth) = bitTpe.hargs.head
    val DataInstance(fromTpe, refer) = from
    val HPElem.Num(fromWidth) = fromTpe.hargs.head
    val casted =
      if(toWidth > fromWidth) ir.DoPrim(PrimOps.Pad, Seq(refer), Seq(toWidth - fromWidth), ir.UnknownType)
      else ir.DoPrim(PrimOps.Bits, Seq(refer), Seq(toWidth - 1, 0), ir.UnknownType)
    val retTpe = toBackendType(Type.bitTpe(toWidth))
    val retInstance = DataInstance(retTpe, casted)

    RunResult(Future.empty, Vector.empty, retInstance)
  }

  private def intBinOps(left: Instance, right: Instance, ops: ir.PrimOp, global: GlobalData)(f: (BigInt, BigInt) => BigInt): RunResult = {
    val DataInstance(tpe, l) = left
    val DataInstance(_, r) = right

    val ret = (l, r) match {
      case (ir.UIntLiteral(left, _), ir.UIntLiteral(right, _)) => ir.UIntLiteral(f(left, right), ir.IntWidth(32))
      case (left, right) => ir.DoPrim(ops, Seq(left, right), Seq.empty, ir.UIntType(ir.IntWidth(32)))
    }

    RunResult.inst(DataInstance(tpe, ret))
  }

  private def intCmpOps(left: Instance, right: Instance, ops: ir.PrimOp, global: GlobalData)(f: (BigInt, BigInt) => Boolean): RunResult = {
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
    RunResult.inst(DataInstance(boolTpe, ret))
  }

  private def intUnaryOps(operand: Instance, ops: ir.PrimOp, global: GlobalData)(f: BigInt => BigInt): RunResult = {
    val ret = operand match {
      case DataInstance(_, ir.UIntLiteral(value, _)) => ir.UIntLiteral(f(value), ir.IntWidth(32))
      case DataInstance(_, expr) => ir.DoPrim(ops, Seq(expr), Seq.empty, ir.UIntType(ir.IntWidth(32)))
    }

    RunResult.inst(DataInstance(operand.tpe, ret))
  }

  private def boolBinOps(left: Instance, right: Instance, ops: ir.PrimOp, global: GlobalData)(f: (Boolean, Boolean) => Boolean): RunResult = {
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

    RunResult.inst(DataInstance(tpe, retRef))
  }

  private def boolUnaryOps(operand: Instance, ops: ir.PrimOp, global: GlobalData)(f: Boolean => Boolean): RunResult = {
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

    RunResult.inst(DataInstance(operand.tpe, ret))
  }

  private def bitBinOps(left: Instance, right: Instance, ops: ir.PrimOp): RunResult = {
    val DataInstance(tpe, leftRef) = left
    val DataInstance(_, rightRef) = right

    RunResult.inst(DataInstance(tpe, ir.DoPrim(ops, Seq(leftRef, rightRef), Seq.empty, ir.UnknownType)))
  }

  private def bitCmpOps(left: Instance, right: Instance, ops: ir.PrimOp, global: GlobalData): RunResult = {
    val DataInstance(_, leftRef) = left
    val DataInstance(_, rightRef) = right

    val retTpe = toBackendType(Type.bitTpe(1)(global))(global)

    RunResult.inst(DataInstance(retTpe, ir.DoPrim(ops, Seq(leftRef, rightRef), Seq.empty, ir.UnknownType)))
  }

  private def bitUnaryOps(operand: Instance, ops: ir.PrimOp): RunResult = {
    val DataInstance(tpe, ref) = operand

    RunResult.inst(DataInstance(tpe, ir.DoPrim(ops, Seq(ref), Seq.empty, ir.UnknownType)))
  }
}
