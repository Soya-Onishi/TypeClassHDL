package tchdl.ast

import tchdl.util.TchdlException.ImplementationErrorException
import tchdl.util.{Constraint, Modifier, RangeEdge, Symbol, Type, Error}

import scala.math.Ordering

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
sealed trait HPExpr extends Expression {
  // This method organizes an expression when an expression is sortable format.
  // TODO:
  //  For now, this method just returns `this`.
  //  Implement actual process.
  def sort: HPExpr = this

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
      case _ => false
    }
}

object HPExpr {
  def verifyHPBound(
    calledBounds: Vector[HPBound],
    callerBounds: Vector[HPBound],
    table: Map[Symbol.HardwareParamSymbol, HPExpr]
  ): Either[Error, Unit] = {
    def replaceExpr(expr: HPExpr, table: Map[Symbol.HardwareParamSymbol, HPExpr]): HPExpr = {
      def loop(expr: HPExpr): HPExpr = {
        expr match {
          case binop @ HPBinOp(op, left, right) =>
            HPBinOp(op, loop(left), loop(right))
              .setTpe(binop.tpe)
              .setID(binop.id)
          case ident: Ident =>
            table.getOrElse(
              ident.symbol.asHardwareParamSymbol,
              throw new ImplementationErrorException(s"try to lookup ${ident.name} but not found")
            )
          case lit => lit
        }
      }

      loop(expr).sort
    }

    def compoundBounds(bounds: Vector[HPBound]): Vector[HPBound] = {
      def removeFirst[T](vec: Vector[T])(f: T => Boolean): (Vector[T], Option[T]) = {
        vec.foldLeft((Vector.empty[T], Option.empty[T])) {
          case ((returnedVec, Some(first)), elem) => (returnedVec :+ elem, Some(first))
          case ((returnedVec, None), elem) if f(elem) => (returnedVec, Some(elem))
          case ((returnedVec, None), elem) => (returnedVec :+ elem, None)
        }
      }

      bounds.foldLeft(Vector.empty[HPBound]) {
        case (bounds, compoundedBound) =>
          val (remainBounds, foundBound) = removeFirst(bounds) {
            case HPBound(expr, _) => expr.isSameExpr(compoundedBound.target)
          }

          foundBound match {
            case None => remainBounds :+ compoundedBound
            case Some(bound) =>
              def isRejected(c: ConstraintExpr): Boolean = bound.constraints.exists(_.isRestrictedThanEq(c))

              val constraints = compoundedBound.constraints.filterNot(isRejected)
              val restrictedBound = constraints.foldLeft(bound) {
                case (bound, constraint) =>
                  val (remain, _) = removeFirst(bound.constraints)(constraint.isRestrictedThanEq)
                  val newConstraints = remain :+ constraint

                  HPBound(bound.target, newConstraints)
              }

              remainBounds :+ restrictedBound
          }
      }
    }

    def findBound(target: HPExpr, bounds: Vector[HPBound]): Option[HPBound] =
      bounds.find {
        bound => bound.target.isSameExpr(target)
      }

    def verifyBound(pairs: Vector[(HPBound, Option[HPBound])]): Either[Error, Unit] = {
      val results = pairs.map {
        case (calledBound, None) => Left(???) // Error represents caller argument bound does not meet called bound
        case (calledBound, Some(callerBound)) =>
          val isMeetAllBounds = calledBound.constraints.forall {
            calledConstraint => callerBound
              .constraints
              .exists(_.isRestrictedThanEq(calledConstraint))
          }

          if(isMeetAllBounds) Right(())
          else Left(???)
      }

      val (errs, _) = results.partitionMap(identity)

      if(errs.isEmpty) Right(())
      else Left(Error.MultipleErrors(errs))
    }

    val replacedCalledBounds = compoundBounds(calledBounds.map {
      case HPBound(target, constraints) =>
        val replacedTarget = replaceExpr(target, table)
        val replacedConstraints = constraints.map(_.map(replaceExpr(_, table)))

        HPBound(replacedTarget, replacedConstraints)
    })

    val pairs = replacedCalledBounds.map { bound => (bound, findBound(bound.target, callerBounds)) }
    verifyBound(pairs)
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
case class TPBound(target: String, constraints: Vector[TypeTree]) extends Bound
case class HPBound(target: HPExpr, constraints: Vector[ConstraintExpr]) extends Bound

trait ConstraintExpr {
  val expr: HPExpr

  def isRestrictedThanEq(that: ConstraintExpr): Boolean = {
    import ConstraintExpr._

    (this, that) match {
      case (LT(IntLiteral(left)), LT(IntLiteral(right))) => left <= right
      case (LT(IntLiteral(left)), LE(IntLiteral(right))) => left < right
      case (LE(IntLiteral(left)), LT(IntLiteral(right))) => left <= right
      case (LE(IntLiteral(left)), LE(IntLiteral(right))) => left <= right
      case (GT(IntLiteral(left)), GT(IntLiteral(right))) => left >= right
      case (GT(IntLiteral(left)), GE(IntLiteral(right))) => left > right
      case (GE(IntLiteral(left)), GT(IntLiteral(right))) => left >= right
      case (GE(IntLiteral(left)), GE(IntLiteral(right))) => left >= right
      case (LT(left), LE(right)) => left.isSameExpr(right)
      case (LE(left), LE(right)) => left.isSameExpr(right)
      case (GT(left), GE(right)) => left.isSameExpr(right)
      case (GE(left), GE(right)) => left.isSameExpr(right)
      case _ => false
    }
  }

  def compound(that: ConstraintExpr): Vector[ConstraintExpr] = {
    import ConstraintExpr._

    def leftIsRestricted(left: ConstraintExpr, right: ConstraintExpr): Boolean =
      (left, right) match {
        case (LT(IntLiteral(left)), LT(IntLiteral(right))) => left < right
        case (LT(IntLiteral(left)), LE(IntLiteral(right))) => left < right
        case (LE(IntLiteral(left)), LT(IntLiteral(right))) => left <= right
        case (LE(IntLiteral(left)), LE(IntLiteral(right))) => left < right
        case (GT(IntLiteral(left)), GT(IntLiteral(right))) => left > right
        case (GT(IntLiteral(left)), GE(IntLiteral(right))) => left > right
        case (GE(IntLiteral(left)), GT(IntLiteral(right))) => left >= right
        case (GE(IntLiteral(left)), GE(IntLiteral(right))) => left > right
        case (LT(left), LE(right)) => left.isSameExpr(right)
        case (GT(left), GE(right)) => left.isSameExpr(right)
        case _ => false
      }

    if(leftIsRestricted(this, that)) Vector(this)
    else if(leftIsRestricted(that, this)) Vector(that)
    else Vector(this, that)
  }

  def map(f: HPExpr => HPExpr): ConstraintExpr
}
object ConstraintExpr {
  case class EQ(expr: HPExpr) extends ConstraintExpr {
    def map(f: HPExpr => HPExpr): ConstraintExpr = { EQ(f(expr)) }
  }

  case class NE(expr: HPExpr) extends ConstraintExpr {
    def map(f: HPExpr => HPExpr): ConstraintExpr = { NE(f(expr)) }
  }

  case class LE(expr: HPExpr) extends ConstraintExpr {
    def map(f: HPExpr => HPExpr): ConstraintExpr = { LE(f(expr)) }
  }

  case class LT(expr: HPExpr) extends ConstraintExpr {
    def map(f: HPExpr => HPExpr): ConstraintExpr = { LT(f(expr)) }
  }

  case class GE(expr: HPExpr) extends ConstraintExpr {
    def map(f: HPExpr => HPExpr): ConstraintExpr = { GE(f(expr)) }
  }

  case class GT(expr: HPExpr) extends ConstraintExpr {
    def map(f: HPExpr => HPExpr): ConstraintExpr = { GT(f(expr)) }
  }
}

case class Ident(name: String) extends Expression with TypeAST with HasSymbol with HPExpr
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
  left: Expression with HPExpr,
  right: Expression with HPExpr
) extends BinOp with HPExpr {
  type Expr = Expression with HPExpr
}

case class Select(expr: Expression, name: String) extends Expression with HasSymbol
case class StaticSelect(suffix: TypeTree, name: String) extends Expression with TypeAST
case class Block(elems: Vector[BlockElem], last: Expression) extends Expression
case class Construct(name: TypeTree, pairs: Vector[ConstructPair]) extends Expression
case class ConstructPair(name: String, expr: Expression) extends AST
case class Self() extends Expression
case class IfExpr(cond: Expression, conseq: Expression, alt: Option[Expression]) extends Expression
case class BitLiteral(value: BigInt, length: Int) extends Expression
case class IntLiteral(value: Int) extends Expression with HPExpr
case class UnitLiteral() extends Expression
case class StringLiteral(str: String) extends Expression with HPExpr

case class Finish() extends Expression
case class Goto(target: String) extends Expression
case class Generate(target: String, params: Vector[Expression]) extends Expression
case class Relay(target: String, params: Vector[Expression]) extends Expression

// To make easier to implement parser,
// hp's length and tp's length maybe incorrect before Typer.
// However, hp's length + tp's length is correct if there is no compile error.
// In Typer, hp and tp are adjust their length
// (as actual procedures, some hp's elements are translate into TypeTree and moved to `tp`)
case class TypeTree(expr: TypeAST, hp: Vector[HPExpr], tp: Vector[TypeTree]) extends AST with HasType with HasSymbol
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