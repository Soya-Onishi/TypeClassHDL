package tchdl.ast

import tchdl.util.Modifier
import tchdl.util.{Type, Symbol, NameSpace}
import tchdl.ASTree


sealed trait AST {
  private var _id: Int = TreeID.id
  def id: Int = this._id
  def setID(num: Int): this.type = {_id = num; this}
}

object TreeID {
  var _id: Int = 0
  def id: Int = {
    val id = _id
    _id += 1
    id
  }
}

sealed trait Component extends AST with Definition
sealed trait Definition extends AST with HasSymbol
sealed trait Statement extends AST
sealed trait BlockElem extends AST
sealed trait Expression extends AST with BlockElem with HasType
sealed trait TypeAST extends AST with HasType


trait HasType {
  private var _tpe: Option[Type] = None
  def tpe: Type = _tpe.get
  def setTpe(tpe: Type): this.type = { _tpe = Some(tpe); this }
}

trait HasSymbol {
  private var _symbol: Option[Symbol] = None
  def symbol: Symbol = _symbol.get
  def setSymbol(symbol: Symbol): this.type = { _symbol = Some(symbol); this }
}

case class CompilationUnit(filename: Option[String], pkgName: Vector[String], topDefs: Vector[Definition]) extends AST

case class ModuleDef(name: String, hp: Vector[ValDef], tp: Vector[TypeDef], bounds: Vector[Bound], parents: Vector[ValDef], siblings: Vector[ValDef], components: Vector[Component]) extends Definition
case class StructDef(name: String, hp: Vector[ValDef], tp: Vector[TypeDef], bounds: Vector[Bound], fields: Vector[ValDef]) extends Definition
case class ImplementClass(target: TypeAST, hp: Vector[ValDef], tp: Vector[TypeDef], bounds: Vector[Bound], methods: Vector[MethodDef], stages: Vector[StageDef]) extends Definition
case class InterfaceDef(name: String, hp: Vector[ValDef], tp: Vector[TypeDef], bounds: Vector[Bound], methods: Vector[MethodDef]) extends Definition
case class ImplementInterface(interface: TypeAST, target: TypeAST, hp: Vector[ValDef], tp: Vector[TypeDef], bounds: Vector[Bound], methods: Vector[MethodDef]) extends Definition
case class AlwaysDef(name: String, blk: Block) extends Component
case class MethodDef(name: String, hp: Vector[ValDef], tp: Vector[TypeDef], bounds: Vector[Bound], params: Vector[ValDef], retTpe: TypeAST, blk: Option[Block]) extends Component
case class ValDef(flag: Modifier, name: String, tpeTree: Option[TypeAST], expr: Option[Expression]) extends Component with BlockElem
case class StageDef(name: String, params: Vector[ValDef], retTpe: TypeAST, states: Vector[StateDef], blk: Vector[BlockElem]) extends Component
case class StateDef(name: String, blk: Block) extends Definition

case class TypeDef(name: String) extends Definition

case class Bound(target: String, constraints: Vector[TypeAST]) extends AST

case class Ident(name: String) extends Expression with HasSymbol
case class ApplyParams(suffix: Expression, args: Vector[Expression]) extends Expression
case class ApplyTypeParams(suffix: Expression, hps: Vector[Expression], tps: Vector[TypeAST]) extends Expression
case class Apply(suffix: Expression, hp: Vector[Expression], tp: Vector[TypeAST], args: Vector[Expression]) extends Expression
case class Select(expr: Expression, name: String) extends Expression with HasSymbol
case class Block(elems: Vector[BlockElem], last: Expression) extends Expression
case class Construct(name: TypeAST, pairs: Vector[ConstructPair]) extends Expression
case class ConstructPair(name: String, expr: Expression) extends AST
case class Self() extends Expression
case class IfExpr(cond: Expression, conseq: Expression, alt: Option[Expression]) extends Expression
case class BitLiteral(value: BigInt, length: Int) extends Expression
case class IntLiteral(value: Int) extends Expression
case class UnitLiteral() extends Expression
case class StringLiteral(str: String) extends Expression

case class Finish() extends Expression
case class Goto(target: String) extends Expression
case class Generate(target: String, params: Vector[Expression]) extends Expression
case class Relay(target: String, params: Vector[Expression]) extends Expression

// To make easier to implement parser,
// hp's length and tp's length maybe incorrect before Typer.
// However, hp's length + tp's length is correct if there is no compile error.
// In Typer, hp and tp are adjust their length
// (as actual procedures, some hp's elements are translate into TypeTree and moved to `tp`)
case class TypeTree(name: String, hp: Vector[Expression], tp: Vector[TypeAST]) extends TypeAST
case class SelfType() extends TypeAST
case class SelectType(suffix: TypeAST, name: String) extends TypeAST