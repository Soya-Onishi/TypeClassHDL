package tchdl.backend.ast

import tchdl.backend._
import tchdl.util._

sealed trait BackendIR
sealed trait Stmt extends BackendIR
sealed trait Expr extends BackendIR with HasType

trait HasType {
  val tpe: BackendType
}

case class Variable(name: String, tpe: BackendType, expr: Expr) extends Stmt
case class Temp(id: Int, expr: Expr) extends Stmt
case class Abandon(expr: Expr) extends Stmt
case class Assign(target: Term.Variable, expr: Expr) extends Stmt
case class Return(expr: Expr) extends Stmt

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
case class CallBuiltIn(label: String, args: Vector[Term], tpe: BackendType) extends Expr
case class CallInterface(label: MethodLabel, accessor: Term, args: Vector[Term], tpe: BackendType) extends Expr

case class This(tpe: BackendType) extends Expr
case class ReferField(accessor: Term, field: FieldLabel, tpe: BackendType) extends Expr

case class Ident(id: Term.Variable, tpe: BackendType) extends Expr
case class IfExpr(cond: Term.Temp, conseq: Vector[Stmt], conseqLast: Expr, alt: Vector[Stmt], altLast: Expr, tpe: BackendType) extends Expr

case class Finish(stage: StageLabel)(implicit global: GlobalData) extends Expr {
  val tpe = toBackendType(Type.unitTpe, Map.empty, Map.empty)
}

case class Goto(state: StateLabel)(implicit global: GlobalData) extends Expr {
  val tpe = toBackendType(Type.unitTpe, Map.empty, Map.empty)
}

case class Generate(stage: StageLabel, args: Vector[Term], tpe: BackendType) extends Expr

case class IntLiteral(value: Int)(implicit global: GlobalData) extends Expr {
  val tpe: BackendType = BackendType (
    global.builtin.types.lookup("Int"),
    Vector.empty,
    Vector.empty
  )
}

case class BitLiteral(value: BigInt, length: HPElem.Num)(implicit global: GlobalData) extends Expr {
  val tpe: BackendType = BackendType (
    global.builtin.types.lookup("Bit"),
    Vector(length),
    Vector.empty,
  )
}

case class UnitLiteral()(implicit global: GlobalData) extends Expr {
  val tpe: BackendType = BackendType(
    global.builtin.types.lookup("Unit"),
    Vector.empty,
    Vector.empty,
  )
}

case class StringLiteral(value: String)(implicit global: GlobalData) extends Expr {
  val tpe: BackendType = BackendType (
    global.builtin.types.lookup("Int"),
    Vector.empty,
    Vector.empty
  )
}

sealed trait Term
object Term {
  case class Variable(name: String, tpe: BackendType) extends Term
  case class Temp(id: Int, tpe: BackendType) extends Term
}


