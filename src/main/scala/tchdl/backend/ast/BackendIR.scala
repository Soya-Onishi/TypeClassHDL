package tchdl.backend.ast

import tchdl.backend._
import tchdl.util._

sealed trait BackendIR
sealed trait Def extends BackendIR with HasType
sealed trait Expr extends BackendIR with HasType

trait HasType {
  val tpe: BackendType
}

case class Variable(name: NameSpace, tpe: BackendType) extends Def
case class Temp(name: String, tpe: BackendType, expr: Expr) extends Def

case class ConstructModule(target: BackendType, parents: Map[String, Expr], siblings: Map[String, Expr]) extends Expr {
  val tpe = target
}

case class ConstructStruct(target: BackendType, pairs: Map[String, Expr]) extends Expr {
  val tpe = target
}

case class Assign(target: Term, expr: Expr) extends BackendIR
case class Return(expr: Expr) extends BackendIR

case class CallMethod(label: MethodLabel, accessor: Option[Term], hargs: Vector[HPElem], args: Vector[Term], tpe: BackendType) extends Expr
case class CallBuiltIn(label: String, args: Vector[Term], tpe: BackendType) extends Expr
case class CallInterface(label: MethodLabel, accessor: Term, args: Vector[Term], tpe: BackendType) extends Expr

case class This(tpe: BackendType) extends Expr
case class ReferField(accessor: Term, field: String, tpe: BackendType) extends Expr

case class Ident(id: Term.Variable, tpe: BackendType) extends Expr
case class IfExpr(cond: Term, conseq: Vector[BackendIR], alt: Vector[BackendIR], tpe: BackendType) extends Expr

case class IntLiteral(value: Int)(implicit global: GlobalData) extends Expr {
  val tpe: BackendType = BackendType (
    global.builtin.types.lookup("Int"),
    Vector.empty,
    Vector.empty
  )
}

case class BitLiteral(value: BigInt, length: HPElem)(implicit global: GlobalData) extends Expr {
  val tpe: BackendType = BackendType (
    global.builtin.types.lookup("Bit"),
    Vector(length),
    Vector.empty
  )
}

case class UnitLiteral()(implicit global: GlobalData) extends Expr {
  val tpe: BackendType = BackendType(
    global.builtin.types.lookup("Unit"),
    Vector.empty,
    Vector.empty
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
  case class Variable(name: NameSpace, tpe: BackendType) extends Term
  case class Node(name: String, tpe: BackendType) extends Term
  case object This extends Term
}


