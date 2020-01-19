package tchdl.ast

import tchdl.util.Modifier

trait AST

trait Component extends AST
trait Definition extends AST
trait Statement extends AST
trait BlockElem
trait Expression extends AST with BlockElem with HasType
trait SupportParamElem extends AST

trait HasType {
  //TODO: tpe field and related methods will be implemented
}

case class ClassDef(name: String, supportParams: List[SupportParamElem], methods: List[MethodDef]) extends Definition
case class InterfaceDef(name: String, supportParams: List[SupportParamElem], components: List[Component]) extends Definition
case class Implement(className: TypeTree, structName: TypeTree, supportParams: List[SupportParamElem], methods: List[MethodDef]) extends Definition

case class ModuleDef(name: String, components: List[AST with Component]) extends Definition
case class StructDef(name: String, supportParams: List[SupportParamElem], fields: List[FieldDef]) extends Definition
case class FieldDef(flag: Modifier, name: String, tpeTree: TypeTree) extends Definition with SupportParamElem with HasType
case class EnumDef(name: String, supportParams: List[SupportParamElem], fields: List[EnumFieldDef]) extends Definition
case class EnumFieldDef(name: String, tpes: List[TypeTree]) extends Definition

case class AlwaysDef(name: String, blk: Block) extends Definition with Component
case class MethodDef(name: String, supportParams: List[SupportParamElem], params: List[FieldDef], retTpe: TypeTree, blk: Option[Block]) extends Definition with Component with HasType
case class ValDef(flag: Modifier, name: String, tpeTree: Option[TypeTree], expr: Option[Expression]) extends Definition with Component with BlockElem
case class StageDef(name: String, params: List[FieldDef], retTpe: TypeTree, states: List[StateDef], blk: Block) extends Definition with Component with HasType
case class StateDef(name: String, blk: Block) extends Definition

case class Ident(name: String) extends Expression
case class Apply(expr: Expression, supportArgs: List[Expression ], args: List[Expression]) extends Expression
case class Select(expr: Expression, name: String) extends Expression
case class Block(elems: List[BlockElem], last: Expression) extends Expression
case class Construct(name: TypeTree, pairs: List[ConstructPair]) extends Expression
case class ConstructPair(name: String, expr: Expression) extends AST
case class Self() extends Expression
case class IfExpr(cond: Expression, conseq: Expression, alt: Option[Expression]) extends Expression
case class Match(expr: Expression, cases: List[Case]) extends Expression
case class Case(cond: AST, conseq: Block) extends AST
case class BitLiteral(value: BigInt, length: Int) extends Expression
case class IntLiteral(value: Int) extends Expression
case class UnitLiteral() extends Expression
case class StringLiteral(str: String) extends Expression

case class Finish() extends AST with Expression
case class Goto(target: String) extends AST with Expression
case class Generate(target: String, params: List[Expression]) extends Expression
case class Relay(target: String, params: List[Expression]) extends Expression

case class TypeTree(name: String, supportParam: List[SupportParamElem]) extends AST with SupportParamElem with HasType

