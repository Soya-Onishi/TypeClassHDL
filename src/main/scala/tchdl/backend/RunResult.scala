package tchdl.backend

import firrtl.ir

case class RunResult(stmts: Vector[ir.Statement], instance: Instance)
object RunResult {
  def inst(instance: Instance): RunResult = RunResult(Vector.empty, instance)
}
