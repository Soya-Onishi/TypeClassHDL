package tchdl.ast

import tchdl.util.TchdlException.ImplementationErrorException
import tchdl.util._

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
sealed trait Literal extends Expression
sealed trait Construct extends Expression with HasSymbol
sealed trait TypeAST extends AST with HasType with HasSymbol
sealed trait ApplyPrefix extends Expression with HasSymbol
sealed trait HPExpr extends Expression {
  protected var _sortedExpr: Option[HPExpr] = None

  // This method organizes an expression when an expression is sortable format.
  def sort: HPExpr = {
    def exec(binop: HPBinOp): HPExpr = {
      def reConstruct(leafs: Vector[HPExpr], op: Operation): HPExpr = {
        val binop = leafs.reduceRight[HPExpr]{
          case (expr, leaf) => HPBinOp(expr, leaf)
        }

        binop._sortedExpr = Some(binop)
        binop
      }

      val leafs = binop.collectLeafs
      val (head, remains) =
        if(binop.op.isCommutative) (Vector.empty, leafs)
        else (Vector(leafs.head), leafs.tail)

      val sortedLeafs = head ++ remains.sortWith {
        case (idLeft @ Ident(left), idRight @ Ident(right)) if left == right => idLeft.symbol.hashCode < idRight.symbol.hashCode
        case (Ident(left), Ident(right)) => left < right
        case (HPUnaryOp(left @ Ident(leftName)), HPUnaryOp(right @ Ident(rightName))) =>
          if(leftName == rightName) left.symbol.hashCode < right.symbol.hashCode
          else leftName < rightName
        case (_: Ident, _) => true
        case (_, _: Ident) => false
        case (_: HPUnaryOp, _) => true
        case (_, _: HPUnaryOp) => false
        case (_: IntLiteral, _: StringLiteral) =>
          val msg = "There is a string literal in hardware parameter expression"
          throw new ImplementationErrorException(msg)
        case (_: StringLiteral, _: IntLiteral) =>
          val msg = "There is a string literal in hardware parameter expression"
          throw new ImplementationErrorException(msg)
        case (IntLiteral(left), IntLiteral(right)) => left < right
        case (StringLiteral(left), StringLiteral(right)) => left < right
      }

      reConstruct(sortedLeafs, binop.op)
    }

    _sortedExpr match {
      case Some(expr) => expr
      case None =>
        val sorted = this match {
          case binOp: HPBinOp => exec(binOp)
          case leaf => leaf
        }

        sorted._sortedExpr = Some(sorted)
        sorted
    }
  }

  // This method expects expressions are already sorted
  def combine: HPExpr = {
    def calc(op: Operation, left: Int, right: Int): Int = {
      val f: (Int, Int) => Int = op match {
        case Operation.Add => _ + _
        case Operation.Sub => _ - _
        case Operation.Mul => _ * _
        case Operation.Div => _ / _
      }

      f(left, right)
    }

    def collectLeafs(expr: HPExpr): Vector[HPExpr] = expr match {
      case HPBinOp(left, right) => collectLeafs(left) ++ collectLeafs(right)
      case leaf => Vector(leaf)
    }

    def reConstruct(leafs: Vector[HPExpr], ops: Operation): HPExpr = leafs match {
      case Vector(leaf) => leaf
      case leafs => HPBinOp(reConstruct(leafs.init, ops), leafs.last)
    }

    def exec(binop: HPBinOp): HPExpr = {
      val leafs = collectLeafs(binop)
      val nums = leafs.collect { case IntLiteral(value) => value }
      val others = leafs.filterNot(_.isInstanceOf[IntLiteral])

      if(nums.isEmpty) binop
      else {
        val combined = IntLiteral(nums.reduce[Int]{ case (l, r) => calc(binop.op, l, r) })
        reConstruct(others :+ combined, binop.op)
      }
    }

    this match {
      case binop: HPBinOp => exec(binop)
      case leaf => leaf
    }
  }

  def isSameExpr(that: HPExpr): Boolean =
    (this.sort, that.sort) match {
      case (l: Ident, r: Ident) => l.symbol == r.symbol
      case (l: HPBinOp, r: HPBinOp) =>
        l.op == r.op &&
          l.left.isSameExpr(r.left) &&
          l.right.isSameExpr(r.right)
      case (l: IntLiteral, r: IntLiteral) => l.value == r.value
      case (_: StringLiteral, _) => throw new ImplementationErrorException("string does not appear here")
      case (_, _: StringLiteral) => throw new ImplementationErrorException("string does not appear here")
      case (HPUnaryOp(left), HPUnaryOp(right)) => left.isSameExpr(right)
      case _ => false
    }

  def replaceWithMap(hpTable: Map[Symbol.HardwareParamSymbol, HPExpr]): HPExpr = {
    def loop(expr: HPExpr): HPExpr = expr match {
      case HPBinOp(left, right) => HPBinOp(loop(left), loop(right))
      case ident: Ident => hpTable.getOrElse(ident.symbol.asHardwareParamSymbol, ident)
      case e => e
    }

    loop(this).sort
  }


  /*
  def disassemble(exprs: Vector[HPExpr]): (Vector[HPExpr], Option[HPExpr]) = {
    def countLeaf(expr: HPExpr): Int = expr match {
      case HPBinOp(_, left, right) => countLeaf(left) + countLeaf(right)
      case _ => 1
    }

    def collectLeaf(expr: HPExpr): Vector[Int] = expr match {
      case HPBinOp(_, left, right) => collectLeaf(left) ++ collectLeaf(right)
      case leaf => Vector(leaf.hashCode)
    }

    def lessThan(v0: Vector[Int], v1: Vector[Int]): Boolean = {
      v0.zip(v1).find{ case (v0, v1) => v0 != v1 } match {
        case Some((v0, v1)) => v0 < v1
        case None => false
      }
    }


    def impl(purged: HPExpr, table: Vector[HPExpr]): (Vector[HPExpr], Option[HPExpr]) = {
      val (hit, remain) = table.foldLeft((Option.empty[HPExpr], Option.empty[HPExpr])) {
        case ((Some(tree), remain), _) => (Some(tree), remain)
        case ((None, None), expr) =>  purged.purge(expr) match {
          case Left(_) => (None, None)
          case Right(remain) => (Some(expr), remain)
        }
      }

      (hit, remain) match {
        case (Some(expr), None) => (Vector(expr), None)
        case (Some(expr), Some(remain)) =>
          val (purgeds, remainExpr) = impl(remain, table)
          (expr +: purgeds, remainExpr)
        case (None, _) => (Vector.empty, Some(purged))
      }
    }


    val (simples, complexes) = exprs.partition(_.isSimpleExpr)
    lazy val simplesTable = simples.sortWith {
      case (e0, e1) =>
        val e0LeafCount = countLeaf(e0)
        val e1LeafCount = countLeaf(e1)
        lazy val e0LeafHashes = collectLeaf(e0)
        lazy val e1LeafHashes = collectLeaf(e1)

        if(e0LeafCount != e1LeafCount) e0LeafCount < e1LeafCount
        else lessThan(e0LeafHashes, e1LeafHashes)
    }.reverse

    if(this.isSimpleExpr) impl(this, complexes ++ simplesTable)
    else (Vector.empty, Some(this))
  }
  */
  /*
  private def purge(expr: HPExpr): Either[Unit, Option[HPExpr]] = {
    def purging(e0: HPExpr, e1: HPExpr): Either[Unit, Option[HPExpr]] = (e0, e1) match {
      case (HPBinOp(_, _), HPBinOp(_, _)) if op0 != op1 => Left(())
      case (HPBinOp(op, left0, right0: Ident), e1 @ HPBinOp(_, left1, right1: Ident)) =>
        if(right0.symbol == right1.symbol) purging(left0, left1) match {
          case Left(()) => Left(())
          case Right(None) => Right(None)
          case Right(Some(remain)) => Right(Some(remain))
        }
        else purging(left0, e1) match {
          case Left(()) => Left(())
          case Right(None) => Right(Some(right0))
          case Right(Some(left)) => Right(Some(HPBinOp(left, right0)))
        }
      case (HPBinOp(left, right: Ident), ident: Ident) =>
        if(right.symbol == ident.symbol) Right(Some(left))
        else purging(left, ident)
      case (id0: Ident, id1: Ident) =>
        if(id0.symbol == id1.symbol) Right(None)
        else Left(())
    }

    if(!expr.isSimpleExpr || !this.isSimpleExpr)
      if(this.isSameExpr(expr)) Right(None)
      else Left(())
    else
      purging(this, expr)
  }
  */

  def swap(table: Map[Symbol.HardwareParamSymbol, HPExpr]): HPExpr = {
    def loop(expr: HPExpr): HPExpr = expr match {
      case HPBinOp(left, right) => HPBinOp(loop(left), loop(right))
      case ident: Ident => table(ident.symbol.asHardwareParamSymbol)
      case lit => lit
    }

    loop(this).sort
  }

  def extractConstant:(HPExpr, Option[Int]) = this.sort.combine match {
    case HPBinOp(left, IntLiteral(right)) => (left, Some(right))
    case expr => (expr, None)
  }

  def negate: HPExpr = this match {
    case HPBinOp(left, right) => HPBinOp(left.negate, right.negate)
    case ident: Ident => HPUnaryOp(ident)
    case HPUnaryOp(ident) => ident
    case IntLiteral(value) => IntLiteral(-value)
  }

  def subtract(that: HPExpr): HPExpr = {
    def collectPosLeafs(expr: HPExpr): Vector[Ident] = expr match {
      case ident: Ident => Vector(ident)
      case HPUnaryOp(_) => Vector.empty
      case HPBinOp(left, right) => collectPosLeafs(left) ++ collectPosLeafs(right)
    }

    def collectNegLeafs(expr: HPExpr): Vector[Ident] = expr match {
      case _: Ident => Vector.empty
      case HPUnaryOp(ident) => Vector(ident)
      case HPBinOp(left, right) => collectNegLeafs(left) ++ collectNegLeafs(right)
    }

    def execSubtract(lefts: Vector[Ident], rights: Vector[Ident]): (Vector[Ident], Vector[Ident]) = {
      val leftSymbols = lefts.map(_.symbol)
      val rightSymbols = rights.map(_.symbol)
      val leftRemains = lefts.filterNot(left => rightSymbols.contains(left.symbol))
      val rightRemains = rights.filterNot(right => leftSymbols.contains(right.symbol))

      (leftRemains, rightRemains)
    }

    val (left, leftConst) = this.sort.combine.extractConstant
    val (right, rightConst) = that.sort.combine.extractConstant
    val leftPosLeafs = collectPosLeafs(left)
    val leftNegLeafs = collectNegLeafs(left)
    val rightPosLeafs = collectPosLeafs(right)
    val rightNegLeafs = collectNegLeafs(right)

    val (leftPosRemains, rightPosRemains) = execSubtract(leftPosLeafs, rightPosLeafs)
    val (leftNegRemains, rightNegRemains) = execSubtract(leftNegLeafs, rightNegLeafs)

    val const = (leftConst, rightConst) match {
      case (Some(left), Some(right)) => Some(IntLiteral(left - right))
      case (Some(left), None)  => Some(IntLiteral(left))
      case (None, Some(right)) => Some(IntLiteral(right))
      case (None, None) => None
    }

    val leafs = leftPosRemains ++ leftNegRemains ++ (rightPosRemains ++ rightNegRemains).map(HPUnaryOp.apply)
    val binop = leafs.reduceLeftOption[HPExpr]{ case (acc, right) => HPBinOp(acc, right) }

    val expr = (binop, const) match {
      case (None, None) => IntLiteral(0)
      case (None, Some(const)) => const
      case (Some(expr), None) => expr
      case (Some(expr), Some(const)) => HPBinOp(expr, const)
    }

    expr.sort.combine
  }

  def countLeafs: Int = this match {
    case HPBinOp(left, right) => left.countLeafs + right.countLeafs
    case HPUnaryOp(_) => 1
    case Ident(_) => 1
    case _: Literal => 1
  }

  def collectLeafs: Vector[HPExpr] = this match {
    case lit: Literal => Vector(lit)
    case op: HPUnaryOp => Vector(op)
    case ident: Ident => Vector(ident)
    case HPBinOp(left, right) => left.collectLeafs ++ right.collectLeafs
  }

  override def hashCode: Int = this match {
    case ident: Ident => ident.symbol.hashCode
    case HPBinOp(left, right) => left.hashCode + right.hashCode
    case HPUnaryOp(expr) => HPUnaryOp.getClass.hashCode + expr.hashCode
    case lit: Literal => lit.hashCode
  }
}

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

case class CompilationUnit(filename: Option[String], pkgName: Vector[String], imports: Vector[Vector[String]], topDefs: Vector[Definition]) extends AST {
  override def toString: String = s"CU[${filename.get}, ${pkgName.mkString("::")}]"
}

case class ModuleDef(name: String, hp: Vector[ValDef], tp: Vector[TypeDef], bounds: Vector[BoundTree], parents: Vector[ValDef], siblings: Vector[ValDef]) extends Definition
case class StructDef(name: String, hp: Vector[ValDef], tp: Vector[TypeDef], bounds: Vector[BoundTree], fields: Vector[ValDef]) extends Definition
case class InterfaceDef(flag: Modifier, name: String, hp: Vector[ValDef], tp: Vector[TypeDef], bounds: Vector[BoundTree], methods: Vector[MethodDef], types: Vector[TypeDef]) extends Definition
case class EnumDef(name: String, hp: Vector[ValDef], tp: Vector[TypeDef], bounds: Vector[BoundTree], members: Vector[EnumMemberDef]) extends Definition
case class EnumMemberDef(name: String, fields: Vector[TypeTree]) extends Definition
case class ImplementClass(target: TypeTree, hp: Vector[ValDef], tp: Vector[TypeDef], bounds: Vector[BoundTree], components: Vector[Component]) extends Definition
case class ImplementInterface(interface: TypeTree, target: TypeTree, hp: Vector[ValDef], tp: Vector[TypeDef], bounds: Vector[BoundTree], methods: Vector[MethodDef], types: Vector[TypeDef]) extends Definition
case class AlwaysDef(name: String, blk: Block) extends Component
case class MethodDef(annons: Vector[Annotation], flag: Modifier, name: String, hp: Vector[ValDef], tp: Vector[TypeDef], bounds: Vector[BoundTree], params: Vector[ValDef], retTpe: TypeTree, blk: Option[Block]) extends Component
case class ValDef(flag: Modifier, name: String, tpeTree: Option[TypeTree], expr: Option[Expression]) extends Component with BlockElem
case class StageDef(name: String, params: Vector[ValDef], retTpe: TypeTree, states: Vector[StateDef], blk: Vector[BlockElem]) extends Component
case class StateDef(name: String, params: Vector[ValDef], blk: Block) extends Definition
case class TypeDef(flag: Modifier, name: String, tpe: Option[TypeTree]) extends Definition

trait ImplicitHPRange
object ImplicitHPRange {
  case object NotInit extends ImplicitHPRange
  case object Invalid extends ImplicitHPRange
  case class Range(max: Option[Int], min: Option[Int]) extends ImplicitHPRange
}

trait BoundTree extends AST
case class TPBoundTree(target: TypeTree, bounds: Vector[TypeTree]) extends BoundTree
case class HPBoundTree(target: HPExpr, bounds: Vector[RangeExpr]) extends BoundTree

trait RangeExpr {
  val expr: HPExpr

  def map(f: HPExpr => HPExpr): RangeExpr = {
    this match {
      case RangeExpr.EQ(expr) => RangeExpr.EQ(f(expr))
      case RangeExpr.Min(expr) => RangeExpr.Min(f(expr))
      case RangeExpr.Max(expr) => RangeExpr.Max(f(expr))
    }
  }
}
object RangeExpr {
  case class EQ(expr: HPExpr) extends RangeExpr
  case class Min(expr: HPExpr) extends RangeExpr
  case class Max(expr: HPExpr) extends RangeExpr
}

case class Ident(name: String) extends Expression with TypeAST with HasSymbol with HPExpr with ApplyPrefix
case class Apply(prefix: ApplyPrefix, hps: Vector[HPExpr], tps: Vector[TypeTree], args: Vector[Expression]) extends Expression

abstract class UnaryOp extends Expression with HasSymbol {
  type Expr <: Expression

  val op: Operation
  val operand: Expr
}

case class StdUnaryOp(op: Operation, operand: Expression) extends UnaryOp {
  type Expr = Expression
}

case class HPUnaryOp(operand: Ident) extends UnaryOp with HPExpr {
  type Expr = Ident
  val op = Operation.Neg
}

abstract class BinOp extends Expression with HasSymbol {
  type Expr <: Expression

  val op: Operation
  val left: Expr
  val right: Expr
}

case class StdBinOp(op: Operation, left: Expression, right: Expression) extends BinOp {
  type Expr = Expression
}

case class HPBinOp(
  left: Expression with HPExpr,
  right: Expression with HPExpr
) extends BinOp with HPExpr {
  type Expr = Expression with HPExpr
  val op: Operation = Operation.Add
}

case class Select(prefix: Expression, name: String) extends Expression with HasSymbol with ApplyPrefix
case class StaticSelect(prefix: TypeTree, name: String) extends Expression with TypeAST with ApplyPrefix
case class CastExpr(expr: Expression, to: TypeTree) extends Expression
case class SelectPackage(packages: Vector[String], name: String) extends AST with TypeAST with Expression
case class Block(elems: Vector[BlockElem], last: Expression) extends Expression
case class ConstructClass(target: TypeTree, fields: Vector[ConstructPair]) extends Construct
case class ConstructModule(target: TypeTree, parents: Vector[ConstructPair], siblings: Vector[ConstructPair]) extends Construct
case class ConstructEnum(target: TypeTree, fields: Vector[Expression]) extends Construct
case class ConstructPair(name: String, init: Expression) extends AST
case class Assign(left: Expression, right: Expression) extends BlockElem

case class This() extends Expression
case class IfExpr(cond: Expression, conseq: Expression, alt: Option[Expression]) extends Expression

case class BitLiteral(value: BigInt, length: Int) extends Literal
case class IntLiteral(value: Int) extends Literal with HPExpr
case class BoolLiteral(value: Boolean) extends Literal with HPExpr
case class UnitLiteral() extends Literal
case class StringLiteral(str: String) extends Literal with HPExpr

case class Finish() extends Expression
case class Goto(target: String, args: Vector[Expression]) extends Expression with HasSymbol

case class Generate(target: String, args: Vector[Expression], state: Option[StateInfo]) extends Expression with HasSymbol
case class Relay(target: String, params: Vector[Expression], state: Option[StateInfo]) extends Expression with HasSymbol
case class StateInfo(target: String, args: Vector[Expression]) extends AST with HasSymbol

case class Return(expr: Expression) extends Expression

case class Match(expr: Expression, cases: Vector[Case]) extends Expression
case class Case(pattern: MatchPattern, exprs: Vector[BlockElem]) extends AST with HasType

trait MatchPattern extends AST
case class EnumPattern(variant: TypeTree, patterns: Vector[MatchPattern]) extends MatchPattern
case class LiteralPattern(lit: Literal) extends MatchPattern
case class IdentPattern(ident: Ident) extends MatchPattern
case class WildCardPattern() extends MatchPattern with HasType

// To make easier to implement parser,
// hp's length and tp's length maybe incorrect before Typer.
// However, hp's length + tp's length is correct if there is no compile error.
// In Typer, hp and tp are adjust their length
// (as actual procedures, some hp's elements are translate into TypeTree and moved to `tp`)
case class TypeTree(expr: TypeAST, hp: Vector[HPExpr], tp: Vector[TypeTree]) extends AST with HasType with HasSymbol
case class ThisType() extends TypeAST with HasType
case class CastType(from: TypeTree, to: TypeTree) extends TypeAST with HasType

trait Operation {
  def toInterface: String
  def toMethod: String
  def toOperator: String
  def isCommutative: Boolean
}

object Operation {
  case object Add extends Operation {
    override def toInterface: String = "Add"
    override def toMethod: String = "add"
    override def toOperator: String = "+"
    override def isCommutative: Boolean = true
  }

  case object Sub extends Operation {
    override def toInterface: String = "Sub"
    override def toMethod: String = "sub"
    override def toOperator: String = "-"
    override def isCommutative: Boolean = false
  }

  case object Mul extends Operation {
    override def toInterface: String = "Mul"
    override def toMethod: String = "mul"
    override def toOperator: String = "*"
    override def isCommutative: Boolean = true
  }

  case object Div extends Operation {
    override def toInterface: String = "Div"
    override def toMethod: String = "div"
    override def toOperator: String = "/"
    override def isCommutative: Boolean = false
  }

  case object Eq extends Operation {
    override def toInterface: String = "Eq"
    override def toMethod: String = "equal"
    override def toOperator: String = "=="
    override def isCommutative: Boolean = true
  }

  case object Ne extends Operation {
    override def toInterface: String = "Eq"
    override def toMethod: String = "notEqual"
    override def toOperator: String = "!="
    override def isCommutative: Boolean = true
  }

  case object Ge extends Operation {
    override def toInterface: String = "Ord"
    override def toMethod: String = "greaterEqual"
    override def toOperator: String = "<="
    override def isCommutative: Boolean = false
  }

  case object Gt extends Operation {
    override def toInterface: String = "Ord"
    override def toMethod: String = "greaterThan"
    override def toOperator: String = "<"
    override def isCommutative: Boolean = false
  }

  case object Le extends Operation {
    override def toInterface: String = "Ord"
    override def toMethod: String = "lessEqual"
    override def toOperator: String = ">="
    override def isCommutative: Boolean = false
  }

  case object Lt extends Operation {
    override def toInterface: String = "Ord"
    override def toMethod: String = "lessThan"
    override def toOperator: String = ">"
    override def isCommutative: Boolean = false
  }

  case object Shr extends Operation {
    override def toInterface: String = "Shr"
    override def toMethod: String = "shr"
    override def toOperator: String = ">>"
    override def isCommutative: Boolean = false
  }

  case object Shl extends Operation {
    override def toInterface: String = "Shl"
    override def toMethod: String = "shl"
    override def toOperator: String = "<<"
    override def isCommutative: Boolean = false
  }

  case object DynShr extends Operation {
    override def toInterface: String = "DynShr"
    override def toMethod: String = "dynShr"
    override def toOperator: String = ">>>"
    override def isCommutative: Boolean = false
  }

  case object DynShl extends Operation {
    override def toInterface: String = "DynShl"
    override def toMethod: String = "dynShl"
    override def toOperator: String = "<<<"
    override def isCommutative: Boolean = false
  }

  case object Neg extends Operation {
    override def toInterface: String = "Neg"
    override def toMethod: String = "neg"
    override def toOperator: String = "-"
    override def isCommutative: Boolean = false
  }

  case object Not extends Operation {
    override def toInterface: String = "Not"
    override def toMethod: String = "not"
    override def toOperator: String = "!"
    override def isCommutative: Boolean = false
  }
}

trait Annotation
object Annotation {
  case class BuiltIn(name: String, args: Vector[String], ret: String) extends Annotation
}