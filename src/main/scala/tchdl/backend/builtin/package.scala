package tchdl.backend

import tchdl.util.Type
import tchdl.util.Symbol
import tchdl.util.GlobalData
import tchdl.backend.ast.{BackendLIR => lir}
import firrtl.PrimOps
import tchdl.backend.FirrtlCodeGen.StackFrame

package object builtin {
  def intAdd(left: Instance, right: Instance): RunResult = {
    intBinOps(left, right, PrimOps.Add)(_ + _)
  }

  def intSub(left: Instance, right: Instance): RunResult = {
    intBinOps(left, right, PrimOps.Sub)(_ - _)
  }

  def intMul(left: Instance, right: Instance): RunResult = {
    intBinOps(left, right, PrimOps.Mul)(_ * _)
  }

  def intDiv(left: Instance, right: Instance): RunResult = {
    intBinOps(left, right, PrimOps.Div)(_ / _)
  }

  def intOr(left: Instance, right: Instance): RunResult = {
    intBinOps(left, right, PrimOps.Or)(_ | _)
  }

  def intAnd(left: Instance, right: Instance): RunResult = {
    intBinOps(left, right, PrimOps.And)(_ & _)
  }

  def intXor(left: Instance, right: Instance): RunResult = {
    intBinOps(left, right, PrimOps.Xor)(_ ^ _)
  }

  def intShl(left: Instance, right: Instance)(implicit global: GlobalData): RunResult = {
    shift(left, right, PrimOps.Shl, PrimOps.Dshl)
  }

  def intShr(left: Instance, right: Instance)(implicit global: GlobalData): RunResult = {
    shift(left, right, PrimOps.Shr, PrimOps.Dshr)
  }

  def intDynShl(left: Instance, right: Instance)(implicit global: GlobalData): RunResult = {
    shift(left, right, PrimOps.Shl, PrimOps.Dshl)
  }

  def intDynShr(left: Instance, right: Instance)(implicit global: GlobalData): RunResult = {
    shift(left, right, PrimOps.Shr, PrimOps.Dshr)
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

  def boolAnd(left: Instance, right: Instance): RunResult = {
    boolBinOps(left, right, PrimOps.And)(_ & _)
  }

  def boolOr(left: Instance, right: Instance): RunResult = {
    boolBinOps(left, right, PrimOps.Or)(_ | _)
  }

  def boolXor(left: Instance, right: Instance): RunResult = {
    boolBinOps(left, right, PrimOps.Xor)(_ ^ _)
  }

  def boolEq(left: Instance, right: Instance, global: GlobalData): RunResult = {
    boolBinOps(left, right, PrimOps.Eq)(_ == _)
  }

  def boolNe(left: Instance, right: Instance, global: GlobalData): RunResult = {
    boolBinOps(left, right, PrimOps.Neq)(_ != _)
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

  def bitOr(left: Instance, right: Instance): RunResult = {
    bitBinOps(left, right, PrimOps.Or)
  }

  def bitAnd(left: Instance, right: Instance): RunResult = {
    bitBinOps(left, right, PrimOps.And)
  }

  def bitXor(left: Instance, right: Instance): RunResult = {
    bitBinOps(left, right, PrimOps.Xor)
  }

  def bitShl(left: Instance, right: Instance)(implicit global: GlobalData): RunResult = {
    shift(left, right, PrimOps.Shl, PrimOps.Dshl)
  }

  def bitShr(left: Instance, right: Instance)(implicit global: GlobalData): RunResult = {
    shift(left, right, PrimOps.Shr, PrimOps.Dshr)
  }

  def bitDynShl(left: Instance, right: Instance)(implicit global: GlobalData): RunResult = {
    shift(left, right, PrimOps.Shl, PrimOps.Dshl)
  }

  def bitDynShr(left: Instance, right: Instance)(implicit global: GlobalData): RunResult = {
    shift(left, right, PrimOps.Shr, PrimOps.Dshr)
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

    val width = hiIndex - loIndex + 1
    val retTpe = toBackendType(Type.bitTpe(width)(global))(global)
    val truncate = lir.Ops(PrimOps.Bits, Vector(refer), Vector(hiIndex, loIndex), retTpe)

    RunResult.inst(DataInstance(retTpe, truncate))
  }

  def bitBit(operand: Instance, index: HPElem, global: GlobalData): RunResult = {
    val HPElem.Num(idx) = index
    val DataInstance(_, refer) = operand
    val retTpe = toBackendType(Type.bitTpe(1)(global))(global)
    val bit = lir.Ops(PrimOps.Bits, Vector(refer), Vector(idx, idx), retTpe)

    RunResult.inst(DataInstance(retTpe, bit))
  }

  def bitConcat(left: Instance, right: Instance, global: GlobalData): RunResult = {
    val DataInstance(BackendType(_, leftHargs, _, false), l) = left
    val DataInstance(BackendType(_, rightHargs, _, false), r) = right

    val HPElem.Num(leftWidth) = leftHargs.head
    val HPElem.Num(rightWidth) = rightHargs.head
    val width = leftWidth + rightWidth
    val retTpe = toBackendType(Type.bitTpe(width)(global))(global)
    val concat = lir.Ops(PrimOps.Cat, Vector(l, r), Vector.empty, retTpe)

    RunResult.inst(DataInstance(retTpe, concat))
  }

  def vecIdx(accessor: Instance, index: HPElem, global: GlobalData): RunResult = {
    val HPElem.Num(idx) = index
    val DataInstance(tpe, refer) = accessor
    val elemType = tpe.targs.head
    val subIndex = lir.SubIndex(refer, idx, elemType)

    RunResult.inst(DataInstance(elemType, subIndex))
  }

  def vecIdxDyn(accessor: Instance, index: Instance, global: GlobalData): RunResult = {
    val DataInstance(_, idx) = index
    val DataInstance(tpe, refer) = accessor
    val elemType = tpe.targs.head
    val subAccess = lir.SubAccess(refer, idx, elemType)

    RunResult.inst(DataInstance(elemType, subAccess))
  }

  def vecUpdated(accessor: Instance, elem: Instance, index: HPElem)(implicit stack: StackFrame, global: GlobalData): RunResult = {
    val name = stack.next("_VEC_UPDATED")
    val vecTpe = accessor.tpe
    val elemTpe = elem.tpe

    val DataInstance(_, vecRef) = accessor
    val DataInstance(_, elemRef) = elem
    val HPElem.Num(idx) = index

    val wire = lir.Wire(name.name, vecTpe)
    val wireRef = lir.Reference(wire.name, vecTpe)
    val init = lir.Assign(wireRef, vecRef)
    val update = lir.Assign(lir.SubIndex(wireRef, idx, elemTpe), elemRef)

    val stmts = Vector(wire, init, update)
    val instance = DataInstance(accessor.tpe, wireRef)

    RunResult(stmts, instance)
  }

  def vecUpdatedDyn(accessor: Instance, index: Instance, elem: Instance)(implicit stack: StackFrame, global: GlobalData): RunResult = {
    val name = stack.next("_VEC_UPDATED")
    val vecTpe = accessor.tpe
    val elemTpe = elem.tpe

    val DataInstance(_, vecRef) = accessor
    val DataInstance(_, elemRef) = elem
    val DataInstance(_, idxRef) = index

    val wire = lir.Wire(name.name, vecTpe)
    val wireRef = lir.Reference(wire.name, vecTpe)
    val init = lir.Assign(wireRef, vecRef)
    val update = lir.Assign(lir.SubAccess(wireRef, idxRef, elemTpe), elemRef)

    val stmts = Vector(wire, init, update)
    val instance = DataInstance(accessor.tpe, wireRef)

    RunResult(stmts, instance)
  }

  def vecAppend(accessor: Instance, elem: Instance)(implicit stack: StackFrame, global: GlobalData): RunResult = {
    val name = stack.next("_GEN")
    val DataInstance(tpe, accessorRef) = accessor
    val DataInstance(_, elemRef) = elem

    val HPElem.Num(accessorLength) = tpe.hargs.head
    val retTpe = BackendType(tpe.symbol, Vector(HPElem.Num(accessorLength + 1)), tpe.targs, isPointer = false)
    val wire = lir.Wire(name.name, retTpe)
    val wireRef = lir.Reference(wire.name, retTpe)
    val init = ir.PartialConnect(ir.NoInfo, wireRef, accessorRef)
    val last = lir.Assign(lir.SubIndex(wireRef, accessorLength, elem.tpe), elemRef)

    val instance = DataInstance(retTpe, wireRef)
    val stmts = Vector(wire, init, last)
    RunResult(stmts, instance)
  }

  def vecTruncate(accessor: Instance, hpHi: HPElem, hpLo: HPElem)(implicit stack: StackFrame, global: GlobalData): RunResult = {
    val name = stack.next("_GEN")
    val DataInstance(tpe, accessorRef) = accessor
    val HPElem.Num(hi) = hpHi
    val HPElem.Num(lo) = hpLo
    val elemTpe = tpe.targs.head
    val wireTpe = BackendType(tpe.symbol, Vector(HPElem.Num(hi - lo + 1)), Vector(elemTpe), isPointer = false)

    val wire = lir.Wire(name.name, wireTpe)
    val wireRef = lir.Reference(wire.name, wireTpe)
    val locRef = (idx: Int) => lir.SubIndex(wireRef, idx, elemTpe)
    val fromRef = (idx: Int) => lir.SubIndex(accessorRef, idx, elemTpe)

    val connects = (lo to hi).zipWithIndex
      .map{ case (fromIdx, locIdx) => lir.Assign(locRef(locIdx), fromRef(fromIdx)) }
      .toVector

    val instance = DataInstance(wireTpe, wireRef)
    val stmts = wire +: connects

    RunResult(stmts, instance)
  }

  def vecEmpty(vecTpe: BackendType)(implicit stack: StackFrame, global: GlobalData): RunResult = {
    val name = stack.next("_GEN")
    val elemTpe = vecTpe.targs.head
    val retTpe = BackendType(vecTpe.symbol, Vector(HPElem.Num(0)), Vector(elemTpe), isPointer = false)
    val wire = lir.Wire(name.name, retTpe)
    val wireRef = lir.Reference(wire.name, retTpe)
    val instance = DataInstance(retTpe, wireRef)

    RunResult(Vector(wire), instance)
  }

  def bitFromInt(bitTpe: BackendType, from: Instance)(implicit global: GlobalData): RunResult = {
    val HPElem.Num(toWidth) = bitTpe.hargs.head
    val DataInstance(_, refer) = from

    val retTpe = toBackendType(Type.bitTpe(toWidth))
    val casted =
      if(toWidth > 32) lir.Ops(PrimOps.Pad, Vector(refer), Vector(toWidth - 32), retTpe)
      else lir.Ops(PrimOps.Bits, Vector(refer), Vector(toWidth - 1, 0), retTpe)
    val retInstance = DataInstance(retTpe, casted)

    RunResult(Vector.empty, retInstance)
  }

  def bitFromBool(bitTpe: BackendType, from: Instance)(implicit global: GlobalData): RunResult = {
    val HPElem.Num(toWidth) = bitTpe.hargs.head
    val DataInstance(_, refer) = from
    val retTpe = toBackendType(Type.bitTpe(toWidth))
    val casted = lir.Ops(PrimOps.Pad, Vector(refer), Vector(toWidth - 1), retTpe)
    val retInstance = DataInstance(retTpe, casted)

    RunResult(Vector.empty, retInstance)
  }

  def bitFromBit(bitTpe: BackendType, from: Instance)(implicit global: GlobalData): RunResult = {
    val HPElem.Num(toWidth) = bitTpe.hargs.head
    val DataInstance(fromTpe, refer) = from
    val HPElem.Num(fromWidth) = fromTpe.hargs.head

    val retTpe = toBackendType(Type.bitTpe(toWidth))
    val casted =
      if(toWidth > fromWidth) lir.Ops(PrimOps.Pad, Vector(refer), Vector(toWidth - fromWidth), retTpe)
      else lir.Ops(PrimOps.Bits, Vector(refer), Vector(toWidth - 1, 0), retTpe)
    val retInstance = DataInstance(retTpe, casted)

    RunResult(Vector.empty, retInstance)
  }

  private def intBinOps(left: Instance, right: Instance, ops: firrtl.ir.PrimOp)(f: (BigInt, BigInt) => BigInt): RunResult = {
    val DataInstance(tpe, l) = left
    val DataInstance(_, r) = right

    val ret = (l, r) match {
      case (lir.Literal(left, _, _), lir.Literal(right, _, _)) => lir.Literal(f(left, right), 32, l.tpe)
      case (left, right) => lir.Ops(ops, Vector(left, right), Vector.empty, l.tpe)
    }

    RunResult.inst(DataInstance(tpe, ret))
  }

  private def intCmpOps(left: Instance, right: Instance, ops: firrtl.ir.PrimOp, global: GlobalData)(f: (BigInt, BigInt) => Boolean): RunResult = {
    def toInt(bool: Boolean): BigInt =
      if(bool) BigInt(1)
      else     BigInt(0)

    val DataInstance(_, l) = left
    val DataInstance(_, r) = right

    val ret = (l, r) match {
      case (lir.Literal(left, _, _), lir.Literal(right, _, _)) => lir.Literal(toInt(f(left, right)), 32, l.tpe)
      case (left, right) => lir.Ops(ops, Vector(left, right), Vector.empty, l.tpe)
    }

    val boolTpe = toBackendType(Type.boolTpe(global))(global)
    RunResult.inst(DataInstance(boolTpe, ret))
  }

  private def intUnaryOps(operand: Instance, ops: firrtl.ir.PrimOp, global: GlobalData)(f: BigInt => BigInt): RunResult = {
    val ret = operand match {
      case DataInstance(_, lir.Literal(value, _, tpe)) => lir.Literal(f(value), 32, tpe)
      case DataInstance(_, expr) => lir.Ops(ops, Vector(expr), Vector.empty, expr.tpe)
    }

    RunResult.inst(DataInstance(operand.tpe, ret))
  }

  private def boolBinOps(left: Instance, right: Instance, ops: firrtl.ir.PrimOp)(f: (Boolean, Boolean) => Boolean): RunResult = {
    def toBool(lit: BigInt): Boolean = {
      lit.toInt match {
        case 0 => false
        case 1 => true
      }
    }

    def toRef(bool: Boolean): lir.Literal = {
      if(bool) lir.Literal(1, 1, left.tpe)
      else     lir.Literal(0, 1, left.tpe)
    }

    val DataInstance(tpe, leftRef) = left
    val DataInstance(_, rightRef) = right

    val retRef = (leftRef, rightRef) match {
      case (lir.Literal(left, _, _), lir.Literal(right, _, _)) =>
        val ret = f(toBool(left), toBool(right))
        toRef(ret)
      case (left, right) =>
        lir.Ops(ops, Vector(left, right), Vector.empty, left.tpe)
    }

    RunResult.inst(DataInstance(tpe, retRef))
  }

  private def boolUnaryOps(operand: Instance, ops: firrtl.ir.PrimOp, global: GlobalData)(f: Boolean => Boolean): RunResult = {
    def toBool(lit: BigInt): Boolean = {
      lit.toInt match {
        case 0 => false
        case 1 => true
      }
    }

    def toRef(bool: Boolean): lir.Literal = {
      if(bool) lir.Literal(1, 1, operand.tpe)
      else     lir.Literal(0, 1, operand.tpe)
    }

    val DataInstance(_, ref) = operand

    val ret = ref match {
      case lir.Literal(value, _, _) => (toRef _ compose f compose toBool)(value)
      case expr => lir.Ops(ops, Vector(expr), Vector.empty, expr.tpe)
    }

    RunResult.inst(DataInstance(operand.tpe, ret))
  }

  private def bitBinOps(left: Instance, right: Instance, ops: firrtl.ir.PrimOp): RunResult = {
    val DataInstance(tpe, leftRef) = left
    val DataInstance(_, rightRef) = right

    val op = lir.Ops(ops, Vector(leftRef, rightRef), Vector.empty, leftRef.tpe)
    RunResult.inst(DataInstance(tpe, op))
  }

  private def bitCmpOps(left: Instance, right: Instance, ops: firrtl.ir.PrimOp, global: GlobalData): RunResult = {
    val DataInstance(_, leftRef) = left
    val DataInstance(_, rightRef) = right

    val retTpe = toBackendType(Type.bitTpe(1)(global))(global)
    val op = lir.Ops(ops, Vector(leftRef, rightRef), Vector.empty, retTpe)

    RunResult.inst(DataInstance(retTpe, op))
  }

  private def bitUnaryOps(operand: Instance, ops: firrtl.ir.PrimOp): RunResult = {
    val DataInstance(tpe, ref) = operand
    val op = lir.Ops(ops, Vector(ref), Vector.empty, tpe)

    RunResult.inst(DataInstance(tpe, op))
  }

  private def shift(left: Instance, right: Instance, ops: firrtl.ir.PrimOp, dynOps: firrtl.ir.PrimOp)(implicit global: GlobalData): RunResult = {
    val DataInstance(tpe, leftRef) = left
    val calc = right match {
      case DataInstance(_, lir.Literal(shamt, _, _)) => lir.Ops(ops, Vector(leftRef), Vector(shamt), tpe)
      case DataInstance(shamtTpe, rightRef) if shamtTpe == toBackendType(Type.intTpe) =>
        val truncate = lir.Ops(PrimOps.Bits, Vector(rightRef), Vector(18, 0))
        lir.Ops(dynOps, Vector(leftRef, truncate), Vector.empty, tpe)
      case DataInstance(shamtTpe, rightRef) if shamtTpe.symbol == Symbol.bit =>
        val HPElem.Num(width) = shamtTpe.hargs.head

        if(width < 20) lir.Ops(dynOps, Vector(leftRef, rightRef), Vector.empty, tpe)
        else {
          val truncate = lir.Ops(PrimOps.Bits, Vector(rightRef), Vector(18, 0))
          lir.Ops(dynOps, Vector(leftRef, truncate), Vector.empty, tpe)
        }
    }

    val instance = DataInstance(tpe, calc)
    RunResult(Vector.empty, instance)
  }
}
