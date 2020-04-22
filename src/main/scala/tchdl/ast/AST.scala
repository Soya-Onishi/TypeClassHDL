package tchdl.ast

import tchdl.util.Modifier
import tchdl.util.{Type, Symbol, NameSpace}
import tchdl.cloneAST


trait AST

trait Component extends AST {
  this: Definition =>
}

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

@cloneAST case class CompilationUnit(filename: Option[String], pkgName: NameSpace, topDefs: Vector[Definition]) extends AST

@cloneAST case class ModuleDef(name: String, hp: Vector[ValDef], tp: Vector[TypeDef], bounds: Vector[Bound], passedModules: Vector[ValDef], components: Vector[Component]) extends Definition
@cloneAST case class StructDef(name: String, hp: Vector[ValDef], tp: Vector[TypeDef], bounds: Vector[Bound], fields: Vector[ValDef]) extends Definition

@cloneAST case class AlwaysDef(name: String, blk: Block) extends Definition with Component
@cloneAST case class MethodDef(name: String, hp: Vector[ValDef], tp: Vector[TypeDef], bounds: Vector[Bound], params: Vector[ValDef], retTpe: TypeTree, blk: Option[Block]) extends Definition with Component
@cloneAST case class ValDef(flag: Modifier, name: String, tpeTree: Option[TypeTree], expr: Option[Expression]) extends Definition with Component with BlockElem
@cloneAST case class StageDef(name: String, params: Vector[ValDef], retTpe: TypeTree, states: Vector[StateDef], blk: Vector[BlockElem]) extends Definition with Component
@cloneAST case class StateDef(name: String, blk: Block) extends Definition

@cloneAST case class TypeDef(name: String) extends Definition

@cloneAST case class Bound(target: String, constraints: Vector[TypeTree]) extends AST

@cloneAST case class Ident(name: String) extends Expression with HasSymbol
@cloneAST case class ApplyParams(suffix: Expression, args: Vector[Expression]) extends Expression
@cloneAST case class ApplyTypeParams(suffix: Expression, tp: Vector[Expression]) extends Expression
@cloneAST case class Select(expr: Expression, name: String) extends Expression
@cloneAST case class Block(elems: Vector[BlockElem], last: Expression) extends Expression
@cloneAST case class Construct(name: TypeTree, pairs: Vector[ConstructPair]) extends Expression
@cloneAST case class ConstructPair(name: String, expr: Expression) extends AST
@cloneAST case class Self() extends Expression
@cloneAST case class IfExpr(cond: Expression, conseq: Expression, alt: Option[Expression]) extends Expression
@cloneAST case class BitLiteral(value: BigInt, length: Int) extends Expression
@cloneAST case class IntLiteral(value: Int) extends Expression
@cloneAST case class UnitLiteral() extends Expression
@cloneAST case class StringLiteral(str: String) extends Expression

@cloneAST case class Finish() extends Expression
@cloneAST case class Goto(target: String) extends Expression
@cloneAST case class Generate(target: String, params: Vector[Expression]) extends Expression
@cloneAST case class Relay(target: String, params: Vector[Expression]) extends Expression

// TODO: Add hp field for TypeTree
//       For now, there are only name and tp field.
//       However, this probably cause problem after Typer
//       because it may be difficult to detect tp's element (i.e. Expression)
//       as type parameter or hardware parameter
//
//       Before typer, hp: Vector[Expression] has all tree and
//       tp: Vector[TypeTree] has no tree.
@cloneAST case class TypeTree(name: String, tp: Vector[Expression]) extends AST with HasType