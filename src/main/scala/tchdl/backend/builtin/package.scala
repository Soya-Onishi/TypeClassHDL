package tchdl.backend

import tchdl.util.{GlobalData, Symbol, ToOption, Type}
import tchdl.backend.ast.{BackendLIR => lir}
import firrtl.PrimOps
import tchdl.backend.StackFrame

package object builtin {
  def intAdd(left: Instance, right: Instance, stack: StackFrame): RunResult = {
    intBinOps(left, right, PrimOps.Add, stack)(_ + _)
  }

  def intSub(left: Instance, right: Instance, stack: StackFrame): RunResult = {
    intBinOps(left, right, PrimOps.Sub, stack)(_ - _)
  }

  def intMul(left: Instance, right: Instance, stack: StackFrame): RunResult = {
    intBinOps(left, right, PrimOps.Mul, stack)(_ * _)
  }

  def intDiv(left: Instance, right: Instance, stack: StackFrame): RunResult = {
    intBinOps(left, right, PrimOps.Div, stack)(_ / _)
  }

  def intOr(left: Instance, right: Instance, stack: StackFrame): RunResult = {
    intBinOps(left, right, PrimOps.Or, stack)(_ | _)
  }

  def intAnd(left: Instance, right: Instance, stack: StackFrame): RunResult = {
    intBinOps(left, right, PrimOps.And, stack)(_ & _)
  }

  def intXor(left: Instance, right: Instance, stack: StackFrame): RunResult = {
    intBinOps(left, right, PrimOps.Xor, stack)(_ ^ _)
  }

  def intShl(left: Instance, right: Instance)(implicit stack: StackFrame, global: GlobalData): RunResult = {
    shift(left, right, PrimOps.Shl, PrimOps.Dshl)
  }

  def intShr(left: Instance, right: Instance)(implicit stack: StackFrame, global: GlobalData): RunResult = {
    shift(left, right, PrimOps.Shr, PrimOps.Dshr)
  }

  def intDynShl(left: Instance, right: Instance)(implicit stack: StackFrame, global: GlobalData): RunResult = {
    shift(left, right, PrimOps.Shl, PrimOps.Dshl)
  }

  def intDynShr(left: Instance, right: Instance)(implicit stack: StackFrame, global: GlobalData): RunResult = {
    shift(left, right, PrimOps.Shr, PrimOps.Dshr)
  }

  def intEq(left: Instance, right: Instance, stack: StackFrame, global: GlobalData): RunResult = {
    intCmpOps(left, right, PrimOps.Eq, stack, global)(_ == _)
  }

  def intNe(left: Instance, right: Instance, stack: StackFrame, global: GlobalData): RunResult = {
    intCmpOps(left, right, PrimOps.Neq, stack, global)(_ != _)
  }

  def intGe(left: Instance, right: Instance, stack: StackFrame, global: GlobalData): RunResult = {
    intCmpOps(left, right, PrimOps.Geq, stack, global)(_ >= _)
  }

  def intGt(left: Instance, right: Instance, stack: StackFrame, global: GlobalData): RunResult = {
    intCmpOps(left, right, PrimOps.Gt, stack, global)(_ > _)
  }

  def intLe(left: Instance, right: Instance, stack: StackFrame, global: GlobalData): RunResult = {
    intCmpOps(left, right, PrimOps.Leq, stack, global)(_ <= _)
  }

  def intLt(left: Instance, right: Instance, stack: StackFrame, global: GlobalData): RunResult = {
    intCmpOps(left, right, PrimOps.Lt, stack, global)(_ < _)
  }

  def intNeg(operand: Instance, stack: StackFrame, global: GlobalData): RunResult = {
    intUnaryOps(operand, PrimOps.Neg, stack, global)(value => -value)
  }

  def intNot(operand: Instance, stack: StackFrame, global: GlobalData): RunResult = {
    intUnaryOps(operand, PrimOps.Not, stack, global)(value => ~value)
  }

  def boolAnd(left: Instance, right: Instance)(implicit stack: StackFrame): RunResult = {
    boolBinOps(left, right, PrimOps.And, stack)(_ & _)
  }

  def boolOr(left: Instance, right: Instance)(implicit stack: StackFrame): RunResult = {
    boolBinOps(left, right, PrimOps.Or, stack)(_ | _)
  }

  def boolXor(left: Instance, right: Instance)(implicit stack: StackFrame): RunResult = {
    boolBinOps(left, right, PrimOps.Xor, stack)(_ ^ _)
  }

  def boolEq(left: Instance, right: Instance, global: GlobalData)(implicit stack: StackFrame): RunResult = {
    boolBinOps(left, right, PrimOps.Eq, stack)(_ == _)
  }

  def boolNe(left: Instance, right: Instance, global: GlobalData)(implicit stack: StackFrame): RunResult = {
    boolBinOps(left, right, PrimOps.Neq, stack)(_ != _)
  }

  def boolNot(operand: Instance, stack: StackFrame, global: GlobalData): RunResult = {
    boolUnaryOps(operand, PrimOps.Not, stack, global)(value => !value)
  }

  def bitAdd(left: Instance, right: Instance)(implicit stack: StackFrame): RunResult = {
    bitBinOps(left, right, PrimOps.Add, stack)
  }

  def bitSub(left: Instance, right: Instance)(implicit stack: StackFrame): RunResult = {
    bitBinOps(left, right, PrimOps.Sub, stack)
  }

  def bitMul(left: Instance, right: Instance)(implicit stack: StackFrame): RunResult = {
    bitBinOps(left, right, PrimOps.Mul, stack)
  }

  def bitDiv(left: Instance, right: Instance)(implicit stack: StackFrame): RunResult = {
    bitBinOps(left, right, PrimOps.Div, stack)
  }

  def bitOr(left: Instance, right: Instance)(implicit stack: StackFrame): RunResult = {
    bitBinOps(left, right, PrimOps.Or, stack)
  }

  def bitAnd(left: Instance, right: Instance)(implicit stack: StackFrame): RunResult = {
    bitBinOps(left, right, PrimOps.And, stack)
  }

  def bitXor(left: Instance, right: Instance)(implicit stack: StackFrame): RunResult = {
    bitBinOps(left, right, PrimOps.Xor, stack)
  }

  def bitShl(left: Instance, right: Instance)(implicit stack: StackFrame, global: GlobalData): RunResult = {
    shift(left, right, PrimOps.Shl, PrimOps.Dshl)
  }

  def bitShr(left: Instance, right: Instance)(implicit stack: StackFrame, global: GlobalData): RunResult = {
    shift(left, right, PrimOps.Shr, PrimOps.Dshr)
  }

  def bitDynShl(left: Instance, right: Instance)(implicit stack: StackFrame, global: GlobalData): RunResult = {
    shift(left, right, PrimOps.Shl, PrimOps.Dshl)
  }

  def bitDynShr(left: Instance, right: Instance)(implicit stack: StackFrame, global: GlobalData): RunResult = {
    shift(left, right, PrimOps.Shr, PrimOps.Dshr)
  }

  def bitEq(left: Instance, right: Instance, stack: StackFrame, global: GlobalData): RunResult = {
    bitCmpOps(left, right, PrimOps.Eq, stack, global)
  }

  def bitNe(left: Instance, right: Instance, stack: StackFrame, global: GlobalData): RunResult = {
    bitCmpOps(left, right, PrimOps.Neq, stack, global)
  }

  def bitGe(left: Instance, right: Instance, stack: StackFrame, global: GlobalData): RunResult = {
    bitCmpOps(left, right, PrimOps.Geq, stack, global)
  }

  def bitGt(left: Instance, right: Instance, stack: StackFrame, global: GlobalData): RunResult = {
    bitCmpOps(left, right, PrimOps.Gt, stack, global)
  }

  def bitLe(left: Instance, right: Instance, stack: StackFrame, global: GlobalData): RunResult = {
    bitCmpOps(left, right, PrimOps.Leq, stack, global)
  }

  def bitLt(left: Instance, right: Instance, stack: StackFrame, global: GlobalData): RunResult = {
    bitCmpOps(left, right, PrimOps.Lt, stack, global)
  }

  def bitNeg(operand: Instance)(implicit stack: StackFrame): RunResult = {
    bitUnaryOps(operand, PrimOps.Neg, stack)
  }

  def bitNot(operand: Instance)(implicit stack: StackFrame): RunResult = {
    bitUnaryOps(operand, PrimOps.Not, stack)
  }

  def bitSignExt(bitTpe: BackendType, operand: Instance, stack: StackFrame, global: GlobalData): RunResult = {
    val HPElem.Num(toWidth) = bitTpe.hargs(0)
    val DataInstance(fromTpe, fromRef) = operand
    val HPElem.Num(fromWidth) =  fromTpe.hargs(0)
    val bit1Tpe = BackendType.bitTpe(1)(global)
    val retTpe = BackendType.bitTpe(toWidth)(global)

    if(toWidth <= fromWidth) {
      val op = lir.Ops(PrimOps.Bits, Vector(fromRef), Vector(toWidth - 1, 0), retTpe)
      val node = lir.Node(stack.next(NameTemplate.temp).name, op, retTpe)
      val instance = DataInstance(retTpe, lir.Reference(node.name, node.tpe))
      RunResult(Vector(node), instance)
    } else {
      val zeroPad = lir.Literal(0, retTpe)
      val onePad = lir.Literal(((BigInt(1) << toWidth) - 1) ^ ((BigInt(1) << fromWidth) - 1), retTpe)
      val zeroNode = lir.Node(stack.next(NameTemplate.temp).name, zeroPad, retTpe)
      val oneNode = lir.Node(stack.next(NameTemplate.temp).name, onePad, retTpe)
      val wireName = stack.next(NameTemplate.temp)
      val padWire = lir.Wire(wireName.name, retTpe)
      val msbExpr = lir.Ops(PrimOps.Head, Vector(fromRef), Vector(1), bit1Tpe)
      val msb = lir.Node(stack.next(NameTemplate.temp).name, msbExpr, bit1Tpe)
      val msbRef = lir.Reference(msb.name, msb.tpe)
      val mux = lir.When(
        msbRef,
        Vector(lir.Assign(lir.Reference(padWire.name, padWire.tpe), lir.Reference( oneNode.name,  oneNode.tpe))),
        Vector(lir.Assign(lir.Reference(padWire.name, padWire.tpe), lir.Reference(zeroNode.name, zeroNode.tpe)))
      )
      val padding = lir.Ops(
        PrimOps.Or,
        Vector(lir.Reference(padWire.name, padWire.tpe), fromRef),
        Vector.empty,
        retTpe
      )
      val paddingNode = lir.Node(
        stack.next(NameTemplate.temp).name,
        padding,
        retTpe
      )

      val stmts = Vector(zeroNode, oneNode, padWire, msb, mux, paddingNode)
      val retRef = lir.Reference(paddingNode.name, paddingNode.tpe)
      val instance = DataInstance(retRef.tpe, retRef)

      RunResult(stmts, instance)
    }
  }

  def bitTruncate(operand: Instance, hi: HPElem, lo: HPElem, stack: StackFrame, global: GlobalData): RunResult = {
    val HPElem.Num(hiIndex) = hi
    val HPElem.Num(loIndex) = lo
    val DataInstance(_, refer) = operand

    val width = hiIndex - loIndex + 1
    val retTpe = toBackendType(Type.bitTpe(width)(global))(global)
    val truncate = lir.Ops(PrimOps.Bits, Vector(refer), Vector(hiIndex, loIndex), retTpe)
    val (truncateNode, truncateRef) = makeNode(truncate, stack)

    RunResult(Vector(truncateNode), DataInstance(retTpe, truncateRef))
  }

  def bitBit(operand: Instance, index: HPElem, stack: StackFrame,global: GlobalData): RunResult = {
    val HPElem.Num(idx) = index
    val DataInstance(_, refer) = operand
    val retTpe = toBackendType(Type.bitTpe(1)(global))(global)
    val bit = lir.Ops(PrimOps.Bits, Vector(refer), Vector(idx, idx), retTpe)
    val (bitNode, bitRef) = makeNode(bit, stack)

    RunResult(Vector(bitNode), DataInstance(retTpe, bitRef))
  }

  def bitConcat(left: Instance, right: Instance, stack: StackFrame, global: GlobalData): RunResult = {
    val DataInstance(BackendType(_, _, leftHargs, _), l) = left
    val DataInstance(BackendType(_, _, rightHargs, _), r) = right

    val HPElem.Num(leftWidth) = leftHargs.head
    val HPElem.Num(rightWidth) = rightHargs.head
    val width = leftWidth + rightWidth
    val retTpe = toBackendType(Type.bitTpe(width)(global))(global)
    val concat = lir.Ops(PrimOps.Cat, Vector(l, r), Vector.empty, retTpe)
    val (concatNode, concatRef) = makeNode(concat, stack)

    RunResult(Vector(concatNode), DataInstance(retTpe, concatRef))
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
    val name = stack.next(NameTemplate.temp)
    val DataInstance(tpe, accessorRef) = accessor
    val DataInstance(_, elemRef) = elem

    val HPElem.Num(accessorLength) = tpe.hargs.head
    val retTpe = BackendType(BackendTypeFlag.NoFlag, tpe.symbol, Vector(HPElem.Num(accessorLength + 1)), tpe.targs)
    val wire = lir.Wire(name.name, retTpe)
    val wireRef = lir.Reference(wire.name, retTpe)
    val init =
      if(accessorLength == 0) None
      else Some(lir.PartialAssign(wireRef, accessorRef))

    val last = lir.Assign(lir.SubIndex(wireRef, accessorLength, elem.tpe), elemRef)

    val instance = DataInstance(retTpe, wireRef)
    val stmts = Vector(Some(wire), init, Some(last)).flatten
    RunResult(stmts, instance)
  }

  def vecTruncate(accessor: Instance, hpHi: HPElem, hpLo: HPElem)(implicit stack: StackFrame, global: GlobalData): RunResult = {
    val name = stack.next("_GEN")
    val DataInstance(tpe, accessorRef) = accessor
    val HPElem.Num(hi) = hpHi
    val HPElem.Num(lo) = hpLo
    val elemTpe = tpe.targs.head
    val wireTpe = BackendType(BackendTypeFlag.NoFlag, tpe.symbol, Vector(HPElem.Num(hi - lo + 1)), Vector(elemTpe))

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
    val retTpe = BackendType(BackendTypeFlag.NoFlag, vecTpe.symbol, Vector(HPElem.Num(0)), Vector(elemTpe))
    val wire = lir.Wire(name.name, retTpe)
    val wireRef = lir.Reference(wire.name, retTpe)
    val instance = DataInstance(retTpe, wireRef)

    RunResult(Vector(wire), instance)
  }

  def bitFromInt(bitTpe: BackendType, from: Instance)(implicit stack: StackFrame, global: GlobalData): RunResult = {
    val HPElem.Num(toWidth) = bitTpe.hargs.head
    val DataInstance(_, refer) = from

    val retTpe = toBackendType(Type.bitTpe(toWidth))
    val casted =
      if(toWidth > 32) lir.Ops(PrimOps.Pad, Vector(refer), Vector(toWidth - 32), retTpe)
      else lir.Ops(PrimOps.Bits, Vector(refer), Vector(toWidth - 1, 0), retTpe)

    val (castedNode, castedRef) = makeNode(casted, stack)
    val retInstance = DataInstance(retTpe, castedRef)

    RunResult(Vector(castedNode), retInstance)
  }

  def bitFromBool(bitTpe: BackendType, from: Instance)(implicit stack: StackFrame, global: GlobalData): RunResult = {
    val HPElem.Num(toWidth) = bitTpe.hargs.head
    val DataInstance(_, refer) = from
    val retTpe = toBackendType(Type.bitTpe(toWidth))
    val casted = lir.Ops(PrimOps.Pad, Vector(refer), Vector(toWidth - 1), retTpe)
    val (castedNode, castedRef) = makeNode(casted, stack)
    val retInstance = DataInstance(retTpe, castedRef)

    RunResult(Vector(castedNode), retInstance)
  }

  def bitFromBit(bitTpe: BackendType, from: Instance)(implicit stack: StackFrame, global: GlobalData): RunResult = {
    val HPElem.Num(toWidth) = bitTpe.hargs.head
    val DataInstance(fromTpe, refer) = from
    val HPElem.Num(fromWidth) = fromTpe.hargs.head

    val retTpe = toBackendType(Type.bitTpe(toWidth))
    val casted =
      if(toWidth > fromWidth) lir.Ops(PrimOps.Pad, Vector(refer), Vector(toWidth - fromWidth), retTpe)
      else lir.Ops(PrimOps.Bits, Vector(refer), Vector(toWidth - 1, 0), retTpe)

    val (castedNode, castedRef) = makeNode(casted, stack)
    val retInstance = DataInstance(retTpe, castedRef)

    RunResult(Vector(castedNode), retInstance)
  }

  private def intBinOps(leftInst: Instance, rightInst: Instance, ops: firrtl.ir.PrimOp, stack: StackFrame)(f: (BigInt, BigInt) => BigInt): RunResult = {
    val DataInstance(tpe, left) = leftInst
    val DataInstance(_, right) = rightInst
    val (retNode, retRef) = makeNode(lir.Ops(ops, Vector(left, right), Vector.empty, left.tpe), stack)

    RunResult(Vector(retNode), DataInstance(tpe, retRef))
  }

  private def intCmpOps(leftInst: Instance, rightInst: Instance, ops: firrtl.ir.PrimOp, stack: StackFrame, global: GlobalData)(f: (BigInt, BigInt) => Boolean): RunResult = {
    val DataInstance(_, left) = leftInst
    val DataInstance(_, right) = rightInst
    val (retNode, retRef) = makeNode(lir.Ops(ops, Vector(left, right), Vector.empty, left.tpe), stack)

    val boolTpe = toBackendType(Type.boolTpe(global))(global)
    RunResult(Vector(retNode), DataInstance(boolTpe, retRef))
  }

  private def intUnaryOps(operand: Instance, ops: firrtl.ir.PrimOp, stack: StackFrame, global: GlobalData)(f: BigInt => BigInt): RunResult = {
    val DataInstance(_, expr) = operand

    val retNode = lir.Node(
      stack.next("_GEN").name,
      lir.Ops(ops, Vector(expr), Vector.empty, expr.tpe),
      expr.tpe
    )
    val retRef = lir.Reference(retNode.name, retNode.tpe)

    RunResult(Vector(retNode), DataInstance(operand.tpe, retRef))
  }

  private def boolBinOps(left: Instance, right: Instance, ops: firrtl.ir.PrimOp, stack: StackFrame)(f: (Boolean, Boolean) => Boolean): RunResult = {
    val DataInstance(tpe, leftRef) = left
    val DataInstance(_, rightRef) = right
    val ret = lir.Ops(ops, Vector(leftRef, rightRef), Vector.empty, left.tpe)
    val retNode = lir.Node(
      stack.next("_GEN").name,
      ret,
      ret.tpe
    )
    val retRef = lir.Reference(retNode.name, retNode.tpe)

    RunResult(Vector(retNode), DataInstance(tpe, retRef))
  }

  private def boolUnaryOps(operand: Instance, ops: firrtl.ir.PrimOp, stack: StackFrame, global: GlobalData)(f: Boolean => Boolean): RunResult = {
    val DataInstance(_, ref) = operand
    val (retNode, retRef) = makeNode(ref, stack)

    RunResult(Vector(retNode), DataInstance(operand.tpe, retRef))
  }

  private def bitBinOps(left: Instance, right: Instance, ops: firrtl.ir.PrimOp, stack: StackFrame): RunResult = {
    val DataInstance(tpe, leftRef) = left
    val DataInstance(_, rightRef) = right

    val op = lir.Ops(ops, Vector(leftRef, rightRef), Vector.empty, leftRef.tpe)
    val (opNode, opRef) = makeNode(op, stack)

    RunResult(Vector(opNode), DataInstance(tpe, opRef))
  }

  private def bitCmpOps(left: Instance, right: Instance, ops: firrtl.ir.PrimOp, stack: StackFrame, global: GlobalData): RunResult = {
    val DataInstance(_, leftRef) = left
    val DataInstance(_, rightRef) = right

    val retTpe = toBackendType(Type.bitTpe(1)(global))(global)
    val op = lir.Ops(ops, Vector(leftRef, rightRef), Vector.empty, retTpe)
    val (opNode, opRef) = makeNode(op, stack)

    RunResult(Vector(opNode), DataInstance(retTpe, opRef))
  }

  private def bitUnaryOps(operand: Instance, ops: firrtl.ir.PrimOp, stack: StackFrame): RunResult = {
    val DataInstance(tpe, ref) = operand
    val op = lir.Ops(ops, Vector(ref), Vector.empty, tpe)
    val (opNode, opRef) = makeNode(op, stack)

    RunResult(Vector(opNode), DataInstance(tpe, opRef))
  }

  private def shift(left: Instance, right: Instance, ops: firrtl.ir.PrimOp, dynOps: firrtl.ir.PrimOp)(implicit stack: StackFrame, global: GlobalData): RunResult = {
    val DataInstance(tpe, leftRef) = left
    val (calc, stmtOpt) = right match {
      case DataInstance(shamtTpe, rightRef) if shamtTpe == toBackendType(Type.intTpe) =>
        val truncate = lir.Ops(PrimOps.Bits, Vector(rightRef), Vector(18, 0), BackendType.bitTpe(19))
        val (truncateNode, truncateRef) = makeNode(truncate, stack)
        val calc = lir.Ops(dynOps, Vector(leftRef, truncateRef), Vector.empty, tpe)

        (calc, truncateNode.some)
      case DataInstance(shamtTpe, rightRef) if shamtTpe.symbol == Symbol.bit =>
        val HPElem.Num(width) = shamtTpe.hargs.head

        if(width < 20) (lir.Ops(dynOps, Vector(leftRef, rightRef), Vector.empty, tpe), Option.empty)
        else {
          val truncate = lir.Ops(PrimOps.Bits, Vector(rightRef), Vector(18, 0), BackendType.bitTpe(19))
          val (truncateNode, truncateRef) = makeNode(truncate, stack)
          val calc = lir.Ops(dynOps, Vector(leftRef, truncateRef), Vector.empty, tpe)

          (calc, truncateNode.some)
        }
    }

    val (calcNode, calcRef) = makeNode(calc, stack)
    val instance = DataInstance(tpe, calcRef)
    RunResult(stmtOpt.toVector :+ calcNode, instance)
  }

  private def makeNode(expr: lir.Expr, stack: StackFrame): (lir.Node, lir.Reference) = {
    val node = lir.Node(
      stack.next("_GEN").name,
      expr,
      expr.tpe
    )
    val ref = lir.Reference(node.name, node.tpe)

    (node, ref)
  }
}
