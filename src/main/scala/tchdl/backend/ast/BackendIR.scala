package tchdl.backend.ast

import tchdl.backend._
import tchdl.util._

sealed trait BackendIR
sealed trait Stmt extends BackendIR { val expr: Expr }
sealed trait Expr extends BackendIR with HasType
sealed trait Literal extends Expr

trait HasType {
  val tpe: BackendType
}

case class Variable(name: String, tpe: BackendType, expr: Expr) extends Stmt
case class Temp(id: Int, expr: Expr) extends Stmt
case class Abandon(expr: Expr) extends Stmt
case class Assign(loc: Vector[(String, BackendType)], expr: Expr) extends Stmt

case class ConstructMemory(name: Term, target: BackendType) extends Expr {
  val tpe = target
}

case class ConstructModule(name: Term, target: BackendType, parents: Map[String, Expr], siblings: Map[String, Expr]) extends Expr {
  val tpe = target
}

case class ConstructStruct(target: BackendType, pairs: Map[String, Expr]) extends Expr {
  val tpe = target
}

case class ConstructEnum(target: BackendType, variant: Symbol.EnumMemberSymbol, passed: Vector[Term.Temp]) extends Expr {
  val tpe = target
}

case class CallMethod(label: MethodLabel, accessor: Option[Term], hargs: Vector[HPElem], args: Vector[Term], tpe: BackendType) extends Expr
case class CallBuiltIn(label: String, accessorTpe: Option[BackendType], args: Vector[Term], hargs: Vector[HPElem], tpe: BackendType) extends Expr
case class CallInterface(label: MethodLabel, accessor: Term, args: Vector[Term], tpe: BackendType) extends Expr
case class ReadMemory(accessor: Term, addr: Term, port: Int, tpe: BackendType) extends Expr
case class WriteMemory(accessor: Term, addr: Term, data: Term, port: Int)(implicit global: GlobalData) extends Expr {
  val tpe: BackendType = BackendType(Symbol.unit, Vector.empty, Vector.empty, isPointer = false)
}

case class This(tpe: BackendType) extends Expr
case class ReferField(accessor: Term, field: FieldLabel, tpe: BackendType) extends Expr

case class Ident(id: Term.Variable, tpe: BackendType) extends Expr
case class Deref(id: Term.Temp, tpe: BackendType) extends Expr
case class IfExpr(cond: Term.Temp, conseq: Vector[Stmt], conseqLast: Expr, alt: Vector[Stmt], altLast: Expr, tpe: BackendType) extends Expr

case class Match(matched: Term.Temp, cases: Vector[Case], tpe: BackendType) extends Expr
case class Case(pattern: MatchPattern, stmts: Vector[Stmt], ret: Expr) extends BackendIR

trait MatchPattern { def tpe: BackendType }
case class IdentPattern(name: Term.Variable) extends MatchPattern { def tpe: BackendType = name.tpe }
case class LiteralPattern(lit: Literal) extends MatchPattern { def tpe: BackendType = lit.tpe }
case class WildCardPattern(tpe: BackendType) extends MatchPattern
case class EnumPattern(variant: Int, patterns: Vector[MatchPattern], tpe: BackendType) extends MatchPattern

case class Finish(stage: StageLabel)(implicit global: GlobalData) extends Expr {
  val tpe = toBackendType(Type.unitTpe, Map.empty, Map.empty)
}

case class Goto(state: State)(implicit global: GlobalData) extends Expr {
  val tpe = toBackendType(Type.unitTpe, Map.empty, Map.empty)
}

case class Generate(stage: StageLabel, args: Vector[Term.Temp], state: Option[State], tpe: BackendType) extends Expr
case class State(label: StateLabel, args: Vector[Term.Temp])

case class Commence(procLabel: ProcLabel, blkLabel: ProcBlockLabel, args: Vector[Term.Temp], tpe: BackendType) extends Expr
case class RelayBlock(procLabel: ProcLabel, blkLabel: ProcBlockLabel, args: Vector[Term.Temp])(implicit global: GlobalData) extends Expr {
  val tpe = toBackendType(Type.unitTpe, Map.empty, Map.empty)
}
case class Return(proc: ProcLabel, expr: Expr)(implicit global: GlobalData) extends Expr {
  val tpe = toBackendType(Type.unitTpe, Map.empty, Map.empty)
}

case class IntLiteral(value: Int)(implicit global: GlobalData) extends Literal {
  val tpe: BackendType = BackendType (Symbol.int, Vector.empty, Vector.empty, isPointer = false)
}

case class BitLiteral(value: BigInt, length: HPElem.Num)(implicit global: GlobalData) extends Literal {
  val tpe: BackendType = BackendType (Symbol.bit, Vector(length), Vector.empty, isPointer = false)
}

case class BoolLiteral(value: Boolean)(implicit global: GlobalData) extends Literal {
  val tpe: BackendType = BackendType (Symbol.bool, Vector.empty, Vector.empty, isPointer = false)
}

case class UnitLiteral()(implicit global: GlobalData) extends Literal {
  val tpe: BackendType = BackendType(Symbol.unit, Vector.empty, Vector.empty, isPointer = false)
}

sealed trait Term { val tpe: BackendType }
object Term {
  case class Variable(name: String, tpe: BackendType) extends Term {
    override def equals(obj: Any): Boolean = obj match {
      case that: Variable => this.name == that.name && this.tpe == that.tpe
      case _ => false
    }
  }

  case class Temp(id: Int, tpe: BackendType) extends Term {
    override def equals(obj: Any): Boolean = obj match {
      case that: Temp => this.id == that.id && this.tpe == that.tpe
      case _ => false
    }
  }
}


