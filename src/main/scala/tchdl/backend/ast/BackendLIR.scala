package tchdl.backend.ast

import tchdl.util.NameSpace
import tchdl.backend._
import firrtl.ir.PrimOp

trait BackendLIR
object BackendLIR {
  trait Dir
  object Dir {
    case object Input extends Dir
    case object Output extends Dir
  }

  trait ComponentType
  object ComponentType {
    case object Node extends ComponentType
    case object Ref extends ComponentType
  }

  trait Stmt extends BackendLIR
  trait Expr extends BackendLIR { val tpe: BackendType }

  case class Module(tpe: BackendType, ports: Vector[Port], subs: Vector[SubModule], mems: Vector[Memory], components: Vector[BackendLIR], inits: Vector[Stmt], procedures: Vector[Stmt]) extends BackendLIR
  case class Port(dir: Dir, name: String, tpe: BackendType) extends BackendLIR
  case class SubModule(name: String, tpe: BackendType) extends BackendLIR
  case class Memory(name: String, readPorts: Int, writePorts: Int, readLatency: Int, writeLatency: Int, size: Int, dataTpe: BackendType, tpe: BackendType)

  case class Wire(name: String, tpe: BackendType) extends Stmt
  case class Node(name: String, src: Expr, tpe: BackendType) extends Stmt
  case class Reg(name: String, default: Expr, tpe: BackendType) extends Stmt
  case class Assign(dst: Expr, src: Expr) extends Stmt
  case class When(cond: Expr, conseq: Vector[BackendLIR], alt: Vector[BackendLIR]) extends Stmt
  case class MemRead(name: String, port: Int, addr: Expr, tpe: BackendType) extends Stmt
  case class MemWrite(name: String, port: Int, addr: Expr, data: Expr) extends Stmt
  case class Stop() extends Stmt

  case class Reference(name: String, tpe: BackendType) extends Expr
  case class SubField(prefix: Expr, name: String, tpe: BackendType) extends Expr
  case class SubIndex(vec: Expr, idx: Int, tpe: BackendType) extends Expr
  case class SubAccess(vec: Expr, idx: Expr, tpe: BackendType) extends Expr
  case class Undef(tpe: BackendType) extends Expr
  case class Literal(value: BigInt, length: Int, tpe: BackendType) extends Expr
  case class Pointer(path: NameSpace, tpe: BackendType) extends Expr
  case class Deref(expr: Expr, tpe: BackendType) extends Expr
  case class Ops(op: PrimOp, args: Vector[Expr], consts: Vector[BigInt], tpe: BackendType) extends Expr
}
