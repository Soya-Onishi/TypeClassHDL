package tchdl.ast

import tchdl.util.Modifier

trait AST

trait Component extends AST
trait Definition extends AST
trait Statement extends AST
trait BlockElem
trait Expression extends AST with BlockElem with HasType
trait SupportParamElem extends AST

trait WorkingAST extends AST

trait HasType {
  //TODO: tpe field and related methods will be implemented
}

case class CompilationUnit(filename: Option[String], topDefs: Array[AST with Definition]) extends AST

case class ClassDef(name: String, hp: Array[FieldDef], tp: Array[TypeDef], bounds: Array[Bound], methods: Array[MethodDef]) extends Definition
case class InterfaceDef(name: String, hp: Array[FieldDef], tp: Array[TypeDef], bounds: Array[Bound], components: Array[Component]) extends Definition
case class Implement(className: TypeTree, target: TypeTree, hp: Array[FieldDef], tp: Array[TypeDef], bounds: Array[Bound], methods: Array[Component]) extends Definition

case class ModuleDef(name: String, hp: Array[FieldDef], tp: Array[TypeDef], bounds: Array[Bound], passedModules: Array[FieldDef], components: Array[Component]) extends Definition
case class StructDef(name: String, hp: Array[FieldDef], tp: Array[TypeDef], bounds: Array[FieldDef], fields: Array[FieldDef]) extends Definition
case class FieldDef(flag: Modifier, name: String, tpeTree: TypeTree) extends Definition with SupportParamElem with HasType
case class EnumDef(name: String, hp: Array[FieldDef], tp: Array[TypeDef], bounds: Array[Bound], fields: Array[EnumFieldDef]) extends Definition
case class EnumFieldDef(name: String, tpes: Array[TypeTree]) extends Definition

case class AlwaysDef(name: String, blk: Block) extends Definition with Component
case class MethodDef(name: String, hp: Array[FieldDef], tp: Array[TypeDef], bounds: Array[Bound], params: Array[FieldDef], retTpe: TypeTree, blk: Option[Block]) extends Definition with Component with HasType
case class ValDef(flag: Modifier, name: String, tpeTree: Option[TypeTree], expr: Option[Expression]) extends Definition with Component with BlockElem
case class StageDef(name: String, params: Array[FieldDef], retTpe: TypeTree, states: Array[StateDef], blk: Array[BlockElem]) extends Definition with Component with HasType
case class StateDef(name: String, blk: Block) extends Definition

case class TypeDef(name: String) extends Definition

case class Bound(target: String, constraints: Array[TypeTree]) extends AST

case class Ident(name: String) extends Expression
case class Apply(name: Expression, hp: Array[Expression], tp: Array[TypeTree], args: Array[Expression]) extends Expression
case class Select(expr: Expression, name: String) extends Expression
case class Block(elems: Array[BlockElem], last: Expression) extends Expression
case class Construct(name: TypeTree, pairs: Array[ConstructPair]) extends Expression
case class ConstructPair(name: String, expr: Expression) extends AST
case class Self() extends Expression
case class IfExpr(cond: Expression, conseq: Expression, alt: Option[Expression]) extends Expression
case class Match(expr: Expression, cases: Array[Case]) extends Expression
case class Case(cond: AST, conseq: Block) extends AST
case class BitLiteral(value: BigInt, length: Int) extends Expression
case class IntLiteral(value: Int) extends Expression
case class UnitLiteral() extends Expression
case class StringLiteral(str: String) extends Expression

case class Finish() extends Expression
case class Goto(target: String) extends Expression
case class Generate(target: String, params: Array[Expression]) extends Expression
case class Relay(target: String, params: Array[Expression]) extends Expression

case class TypeTree(name: String, hp: Array[Expression], tp: Array[TypeTree]) extends AST with SupportParamElem with HasType

object WorkingAST {
  case class HardwareParam(hp: Array[FieldDef]) extends WorkingAST
  case class TypeParam(tp: Array[TypeDef]) extends WorkingAST
  case class Bounds(bounds: Array[Bound]) extends WorkingAST
  case class Inner(inner: Component) extends WorkingAST
  case class FieldDefs(fields: Array[FieldDef]) extends WorkingAST
  case class StageBody(state: Array[StateDef], block: Array[BlockElem]) extends WorkingAST
  case class Modifiers(modifier: Modifier) extends WorkingAST
  case class ComponentBody(name: String, tpe: Option[TypeTree], expr: Option[Expression]) extends WorkingAST
}