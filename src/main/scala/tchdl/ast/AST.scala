package tchdl.ast

import tchdl.util.{Constraint, Modifier, RangeEdge, Symbol, Type}


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
sealed trait TypeAST extends AST with HasType with HasSymbol
sealed trait HardwareParam extends Expression {
  def isSame(that: Expression with HardwareParam): Boolean = {
    val sortedThis = this.simplify.sort
    val sortedThat = that.simplify.sort

    sortedThis == sortedThat
  }

  def contains(expr: Expression with HardwareParam): Boolean = ???

  def sort: Expression with HardwareParam = ???

  def simplify: Expression with HardwareParam = {
    def allSymbols(expr: Expression with HardwareParam): Set[Symbol.HardwareParamSymbol] = expr match {
      case HPBinOp(_, left, right) => allSymbols(left) ++ allSymbols(right)
      case ident: Ident => Set(ident.symbol.asHardwareParamSymbol)
      case _: StringLiteral => Set()
      case _: IntLiteral => Set()
    }

    def replace(tree: Expression with HardwareParam, constraint: Constraint): Expression with HardwareParam = {
      type Tree = Expression with HardwareParam

      val RangeEdge.ThanEq(lit: IntLiteral) = constraint.range.min

      def loop(tree: Tree, target: Tree, rootOp: Operation): Option[Tree] = {
        def verifyLeftAndRight(tree: HPBinOp): Option[Tree] =
          loop(tree.left, target, rootOp) match {
            case Some(left) => Some(HPBinOp(tree.op, left, tree.right))
            case None => loop(tree.right, target, rootOp) match {
              case Some(right) => Some(HPBinOp(tree.op, tree.left, right))
              case None => None
            }
          }

        (tree, target) match {
          case (bTree: HPBinOp, bTarget: HPBinOp) if bTree.op != bTarget.op =>
            verifyLeftAndRight(bTree)
          case (bTree: HPBinOp, bTarget: HPBinOp) if bTree.op == bTarget.op && bTree.op != rootOp =>
            if(bTree == bTarget) Some(lit)
            else verifyLeftAndRight(bTree)
          case (bTree: HPBinOp, bTarget: HPBinOp) /* if bTree.op == bTarget.op && bTree.op == rootOp */ =>
            if(bTree.right == bTarget.right) loop(bTree.left, bTarget.left, rootOp)
            else verifyLeftAndRight(bTree)
          case (bTree: HPBinOp, bTarget: Ident) if bTree.op == rootOp =>
            if(bTree.right == bTarget) Some(HPBinOp(bTree.op, bTree.left, lit))
            else loop(bTree.left, bTarget, rootOp)
          case (bTree: Ident, bTarget: Ident) =>
            if(bTree == bTarget) Some(lit)
            else None
          case _ => ??? // TODO: verify other patterns
        }
      }

      val replaced = constraint.target match {
        case target @ HPBinOp(op, _, _) => loop(tree, target, op)
        case ident: Ident if tree == ident => Some(lit)
        case _ => None
      }

      replaced match {
        case Some(tree) => replace(tree.sort, constraint)
        case None => tree
      }
    }

    def countLeaf(tree: Expression with HardwareParam): Int =
      tree match {
        case _: Ident => 1
        case _: IntLiteral => 1
        case HPBinOp(_, left, right) => countLeaf(left) + countLeaf(right)
      }

    val symbols = allSymbols(this)
    val constraints = symbols.toVector
      .flatMap(_.getBounds(this))
      .filter(_.range.isConstant)
      .foldLeft[Vector[Constraint]](Vector.empty) {
        case (constraints, constraint) if !constraints.map(_.target).contains(constraint.target) =>
          constraints :+ constraint
        case (constraints, _) =>
          constraints
      }
      .sortWith((left, right) => countLeaf(left.target) < countLeaf(right.target))
      .reverse

    constraints.foldLeft(this){
      case (tree, constraint) => replace(tree.sort, constraint)
    }
  }
}
sealed trait HPConstraint

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

case class CompilationUnit(filename: Option[String], pkgName: Vector[String], imports: Vector[Vector[String]], topDefs: Vector[Definition]) extends AST

case class ModuleDef(name: String, hp: Vector[ValDef], tp: Vector[TypeDef], bounds: Vector[Bound], parents: Vector[ValDef], siblings: Vector[ValDef], components: Vector[Component]) extends Definition
case class StructDef(name: String, hp: Vector[ValDef], tp: Vector[TypeDef], bounds: Vector[Bound], fields: Vector[ValDef]) extends Definition
case class ImplementClass(target: TypeTree, hp: Vector[ValDef], tp: Vector[TypeDef], bounds: Vector[Bound], methods: Vector[MethodDef], stages: Vector[StageDef]) extends Definition
case class InterfaceDef(name: String, hp: Vector[ValDef], tp: Vector[TypeDef], bounds: Vector[Bound], methods: Vector[MethodDef]) extends Definition
case class ImplementInterface(interface: TypeTree, target: TypeTree, hp: Vector[ValDef], tp: Vector[TypeDef], bounds: Vector[Bound], methods: Vector[MethodDef]) extends Definition
case class AlwaysDef(name: String, blk: Block) extends Component
case class MethodDef(name: String, hp: Vector[ValDef], tp: Vector[TypeDef], bounds: Vector[Bound], params: Vector[ValDef], retTpe: TypeTree, blk: Option[Block]) extends Component
case class ValDef(flag: Modifier, name: String, tpeTree: Option[TypeTree], expr: Option[Expression]) extends Component with BlockElem
case class StageDef(name: String, params: Vector[ValDef], retTpe: TypeTree, states: Vector[StateDef], blk: Vector[BlockElem]) extends Component
case class StateDef(name: String, blk: Block) extends Definition

case class TypeDef(name: String) extends Definition

trait Bound extends AST
case class TypeParamBound(target: String, constraints: Vector[TypeTree]) extends Bound
case class HardwareParamBound(target: Expression with HardwareParam, constraints: Vector[ConstraintExpr]) extends Bound

trait ConstraintExpr
object ConstraintExpr {
  case class Equal(expr: Expression with HPConstraint) extends ConstraintExpr
  case class LessEq(expr: Expression with HPConstraint) extends ConstraintExpr
  case class LessThan(expr: Expression with HPConstraint) extends ConstraintExpr
  case class GreaterEq(expr: Expression with HPConstraint) extends  ConstraintExpr
  case class GreaterThan(expr: Expression with HPConstraint) extends ConstraintExpr
}

case class Ident(name: String) extends Expression with TypeAST with HasSymbol with HPConstraint with HardwareParam
case class ApplyParams(suffix: Expression, args: Vector[Expression]) extends Expression
case class ApplyTypeParams(suffix: Expression, hps: Vector[Expression], tps: Vector[TypeTree]) extends Expression
case class Apply(suffix: Expression, hp: Vector[Expression], tp: Vector[TypeTree], args: Vector[Expression]) extends Expression

abstract class BinOp extends Expression {
  type Expr <: Expression

  val op: Operation
  val left: Expr
  val right: Expr
}

case class StdBinOp(op: Operation, left: Expression, right: Expression) extends BinOp {
  type Expr = Expression
}

case class HPBinOp(
  op: Operation,
  left: Expression with HardwareParam,
  right: Expression with HardwareParam
) extends BinOp with HardwareParam {
  type Expr = Expression with HardwareParam
}

case class Select(expr: Expression, name: String) extends Expression with HasSymbol
case class StaticSelect(suffix: TypeTree, name: String) extends Expression with TypeAST
case class Block(elems: Vector[BlockElem], last: Expression) extends Expression
case class Construct(name: TypeTree, pairs: Vector[ConstructPair]) extends Expression
case class ConstructPair(name: String, expr: Expression) extends AST
case class Self() extends Expression
case class IfExpr(cond: Expression, conseq: Expression, alt: Option[Expression]) extends Expression
case class BitLiteral(value: BigInt, length: Int) extends Expression
case class IntLiteral(value: Int) extends Expression with HPConstraint with HardwareParam
case class UnitLiteral() extends Expression
case class StringLiteral(str: String) extends Expression with HardwareParam

case class Finish() extends Expression
case class Goto(target: String) extends Expression
case class Generate(target: String, params: Vector[Expression]) extends Expression
case class Relay(target: String, params: Vector[Expression]) extends Expression

// To make easier to implement parser,
// hp's length and tp's length maybe incorrect before Typer.
// However, hp's length + tp's length is correct if there is no compile error.
// In Typer, hp and tp are adjust their length
// (as actual procedures, some hp's elements are translate into TypeTree and moved to `tp`)
case class TypeTree(expr: TypeAST, hp: Vector[Expression], tp: Vector[TypeTree]) extends AST with HasType with HasSymbol
case class SelfType() extends TypeAST

trait Operation {
  def toInterface: String
  def toMethod: String = this.toInterface.toLowerCase
  def toOperator: String
}
object Operation {
  case object Add extends Operation {
    override def toInterface: String = "Add"
    override def toOperator: String = "+"
  }

  case object Sub extends Operation {
    override def toInterface: String = "Sub"
    override def toOperator: String = "-"
  }

  case object Mul extends Operation {
    override def toInterface: String = "Mul"
    override def toOperator: String = "*"
  }

  case object Div extends Operation {
    override def toInterface: String = "Div"
    override def toOperator: String = "/"
  }
}