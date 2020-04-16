package tchdl.ast

import tchdl.util.Modifier
import tchdl.util.{Type, Symbol}

trait AST

trait Component extends AST
trait Definition extends AST with HasSymbol
trait Statement extends AST
trait BlockElem extends AST
trait Expression extends AST with BlockElem with HasType
trait SupportParamElem extends AST

trait WorkingAST extends AST

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

case class CompilationUnit(filename: Option[String], topDefs: Vector[AST with Definition]) extends AST

case class ModuleDef(name: String, hp: Vector[ValDef], tp: Vector[TypeDef], bounds: Vector[Bound], passedModules: Vector[ValDef], components: Vector[Component]) extends Definition
case class StructDef(name: String, hp: Vector[ValDef], tp: Vector[TypeDef], bounds: Vector[Bound], fields: Vector[ValDef]) extends Definition

case class AlwaysDef(name: String, blk: Block) extends Definition with Component
case class MethodDef(name: String, hp: Vector[ValDef], tp: Vector[TypeDef], bounds: Vector[Bound], params: Vector[ValDef], retTpe: TypeTree, blk: Option[Block]) extends Definition with Component with HasType
case class ValDef(flag: Modifier, name: String, tpeTree: Option[TypeTree], expr: Option[Expression]) extends Definition with Component with BlockElem
case class StageDef(name: String, params: Vector[ValDef], retTpe: TypeTree, states: Option[Vector[StateDef]], blk: Option[Vector[BlockElem]]) extends Definition with Component with HasType
case class StateDef(name: String, blk: Block) extends Definition

case class TypeDef(name: String) extends Definition

case class Bound(target: String, constraints: Vector[TypeTree]) extends AST

case class Ident(name: String) extends Expression
case class Apply(name: Expression, tp: Vector[Expression], args: Vector[Expression]) extends Expression
case class Select(expr: Expression, name: String) extends Expression
case class Block(elems: Vector[BlockElem], last: Expression) extends Expression
case class Construct(name: TypeTree, pairs: Vector[ConstructPair]) extends Expression
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

case class TypeTree(name: String, tp: Vector[Expression]) extends AST with HasType

object WorkingAST {
  case class HardwareParam(hp: Vector[ValDef]) extends WorkingAST
  case class TypeParam(tp: Vector[TypeDef]) extends WorkingAST
  case class Bounds(bounds: Vector[Bound]) extends WorkingAST
  case class Inner(inner: Component) extends WorkingAST
  case class FieldDefs(fields: Vector[ValDef]) extends WorkingAST
  case class StageBody(state: Vector[StateDef], block: Vector[BlockElem]) extends WorkingAST
  case class Modifiers(modifier: Modifier) extends WorkingAST
  case class ComponentBody(name: String, tpe: Option[TypeTree], expr: Option[Expression]) extends WorkingAST
}