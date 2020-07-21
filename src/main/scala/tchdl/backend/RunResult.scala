package tchdl.backend

import firrtl.ir

case class RunResult(future: Future, stmts: Vector[ir.Statement], instance: Instance)
object RunResult {
  def inst(instance: Instance): RunResult = RunResult(Future.empty, Vector.empty, instance)
}
