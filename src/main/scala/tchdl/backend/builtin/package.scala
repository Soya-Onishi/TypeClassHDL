package tchdl.backend

import tchdl.backend.FirrtlCodeGen._
import tchdl.util.GlobalData

import firrtl.ir
import firrtl.PrimOps

package object builtin {
  def intIntAdd(left: Instance, right: Instance, global: GlobalData): Instance = {
    intBinOps(left, right, global)(_ + _)
  }

  def intIntSub(left: Instance, right: Instance, global: GlobalData): Instance = {
    intBinOps(left, right, global)(_ - _)
  }

  def intIntMul(left: Instance, right: Instance, global: GlobalData): Instance = {
    intBinOps(left, right, global)(_ * _)
  }

  def intIntDiv(left: Instance, right: Instance, global: GlobalData): Instance = {
    intBinOps(left, right, global)(_ / _)
  }

  def bitBitAdd(left: Instance, right: Instance, global: GlobalData): Instance = {
    bitBinOps(left, right, PrimOps.Add)
  }

  def bitBitSub(left: Instance, right: Instance, global: GlobalData): Instance = {
    bitBinOps(left, right, PrimOps.Sub)
  }

  def bitBitMul(left: Instance, right: Instance, global: GlobalData): Instance = {
    bitBinOps(left, right, PrimOps.Mul)
  }

  def bitBitDiv(left: Instance, right: Instance, global: GlobalData): Instance = {
    bitBinOps(left, right, PrimOps.Div)
  }

  private def intBinOps(left: Instance, right: Instance, global: GlobalData)(f: (Int, Int) => Int): Instance = {
    val IntInstance(l) = left
    val IntInstance(r) = right
    val ret = f(l, r)

    IntInstance(ret)(global)
  }

  private def bitBinOps(left: Instance, right: Instance, ops: ir.PrimOp): Instance = {
    val BitInstance(tpe, leftRef) = left
    val BitInstance(_, rightRef) = right

    BitInstance(tpe, ir.DoPrim(ops, Seq(leftRef, rightRef), Seq.empty, ir.UnknownType))
  }
}
