package tchdl.backend

import tchdl.backend.ast.{BackendLIR => lir}

case class RunResult(stmts: Vector[lir.Stmt], instance: Instance)
object RunResult {
  def inst(instance: Instance): RunResult = RunResult(Vector.empty, instance)
}
