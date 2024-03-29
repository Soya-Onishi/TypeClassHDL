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
  trait Ref extends Expr

  case class Module(tpe: BackendType, ports: Vector[Port], subs: Vector[SubModule], mems: Vector[Memory], components: Vector[Stmt], inits: Vector[Stmt], procedures: Vector[Stmt]) extends BackendLIR
  case class Port(dir: Dir, name: String, tpe: BackendType) extends BackendLIR
  case class SubModule(name: String, tpe: BackendType) extends BackendLIR
  case class Memory(name: String, readPorts: Int, writePorts: Int, readLatency: Int, writeLatency: Int, size: Int, dataTpe: BackendType, tpe: BackendType)

  case class Wire(name: String, tpe: BackendType) extends Stmt
  case class Node(name: String, src: Expr, tpe: BackendType) extends Stmt
  case class Reg(name: String, default: Option[Ref], tpe: BackendType) extends Stmt
  case class IDReg(proc: NameSpace, blk: String, idName: String) extends Stmt
  case class Assign(dst: Ref, src: Ref) extends Stmt
  case class PriorityAssign(dst: Ref, via: String, src: Ref) extends Stmt
  case class PartialAssign(dst: Ref, src: Ref) extends Stmt
  case class Invalid(name: Ref) extends Stmt
  case class When(cond: Ref, conseq: Vector[Stmt], alt: Vector[Stmt]) extends Stmt
  case class MemRead(name: String, port: Int, addr: Ref, tpe: BackendType) extends Stmt
  case class MemWrite(name: String, port: Int, addr: Ref, data: Ref) extends Stmt
  // For default expression return, idRef is Option[Ref] not just Ref
  case class Return(path: NameSpace, expr: Ref, idName: Option[String]) extends Stmt
  case class Deref(name: String, ref: Reference, tpe: BackendType) extends Stmt
  case class PassID(dst: String, from: String) extends Stmt
  case class Stop(msg: String) extends Stmt

  case class Reference(name: String, tpe: BackendType) extends Ref
  case class SubField(prefix: Ref, name: String, tpe: BackendType) extends Ref
  case class SubIndex(vec: Ref, idx: Int, tpe: BackendType) extends Ref
  case class SubAccess(vec: Ref, idx: Ref, tpe: BackendType) extends Ref

  case class Literal(value: BigInt, tpe: BackendType) extends Expr
  case class Commence(path: NameSpace, origin: String, tpe: BackendType) extends Expr
  case class Ops(op: PrimOp, args: Vector[Ref], consts: Vector[BigInt], tpe: BackendType) extends Expr
  case class MemPortID(name: String, port: Int, tpe: BackendType) extends Expr
  case class ProcStepID(proc: String, step: String, tpe: BackendType) extends Expr

  // Below two IRs are for Enum
  case class Concat(subjects: Vector[Ref], tpe: BackendType) extends Expr

  // history's head is newest size(i.e. use length head has to extract bits)
  // tail elements are for calculating index to initiate extracting
  case class Extract(target: Ref, history: Vector[BackendType], tpe: BackendType) extends Expr
}
