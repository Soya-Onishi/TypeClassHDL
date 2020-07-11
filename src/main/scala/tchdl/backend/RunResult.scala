package tchdl.backend

import firrtl.ir

case class RunResult(future: Future, stmts: Vector[ir.Statement], instance: Instance)
