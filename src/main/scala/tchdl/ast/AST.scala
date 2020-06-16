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
sealed trait TypeAST extends AST with HasType with HasSymbol
sealed trait HPExpr extends Expression {
  protected var _sortedExpr: Option[HPExpr] = None

  // This method organizes an expression when an expression is sortable format.
  def sort: HPExpr = {
    def sortChildren: HPExpr = this match {
      case HPBinOp(op, left, right) =>
        val binop = HPBinOp(op, left.sort, right.sort)
        binop._sortedExpr = Some(binop)
        binop
      case others => others
    }

    def exec(binop: HPBinOp): HPExpr = {
      def collectLeafs(expr: HPExpr): Vector[HPExpr] = expr match {
        case HPBinOp(_, left, right) => collectLeafs(left) ++ collectLeafs(right)
        case leaf => Vector(leaf)
      }

      def reConstruct(leafs: Vector[HPExpr], op: Operation): HPExpr = leafs.init match {
        case Vector(leaf) => leaf
        case remains =>
          val binop = HPBinOp(op, reConstruct(remains, op), leafs.last)
          binop._sortedExpr = Some(binop)
          binop
      }

      val leafs = collectLeafs(binop)
      val (head, remains) =
        if(binop.op.isCommutative) (Vector.empty, leafs)
        else (Vector(leafs.head), leafs.tail)

      val sortedLeafs = head ++ remains.sortWith {
        case (idLeft @ Ident(left), idRight @ Ident(right)) if left == right =>
          idLeft.symbol.hashCode < idRight.symbol.hashCode
        case (Ident(left), Ident(right)) => left < right
        case (_: Ident, _) => true
        case (_, _: Ident) => false
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
        val sorted =
          if(!this.isSimpleExpr) sortChildren
          else this match {
            case binOp: HPBinOp => exec(binOp)
            case leaf => leaf
          }

        sorted._sortedExpr = Some(sorted)
        sorted
    }
  }

  // This method expects expressions are already sorted
  def combine: HPExpr = {
    def collectLeafs(expr: HPExpr): Vector[HPExpr] = expr match {
      case HPBinOp(_, left, right) => collectLeafs(left) ++ collectLeafs(right)
      case leaf => Vector(leaf)
    }

    def reConstruct(leafs: Vector[HPExpr], ops: Operation): HPExpr = leafs match {
      case Vector(leaf) => leaf
      case leafs => HPBinOp(ops, reConstruct(leafs.init, ops), leafs.last)
    }

    def exec(binop: HPBinOp): HPExpr = {
      val leafs = collectLeafs(binop)
      val nums = leafs.collect { case IntLiteral(value) => value }
      val others = leafs.filterNot(_.isInstanceOf[IntLiteral])

      val f: (Int, Int) => Int = binop.op match {
        case Operation.Add => _ + _
        case Operation.Sub => _ - _
        case Operation.Mul => _ * _
        case Operation.Div => _ / _
      }

      if(nums.isEmpty) binop
      else {
        val combined = IntLiteral(nums.reduce(f))
        reConstruct(others :+ combined, binop.op)
      }
    }

    if(!this.isSimpleExpr) {
      val HPBinOp(op, left, right) = this
      HPBinOp(op, left.combine, right.combine)
    } else this match {
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
      case _ => false
    }

  def replaceWithMap(hpTable: Map[Symbol.HardwareParamSymbol, HPExpr]): HPExpr = {
    def loop(expr: HPExpr): HPExpr = expr match {
      case HPBinOp(op, left, right) => HPBinOp(op, loop(left), loop(right))
      case ident: Ident => hpTable(ident.symbol.asHardwareParamSymbol)
      case e => e
    }

    loop(this).sort
  }

  private def isSimpleExpr: Boolean = {
    def loop(expr: HPExpr, rootOp: Operation): Boolean = expr match {
      case HPBinOp(op, left, right) =>
        op == rootOp        &&
        loop(left, rootOp)  &&
        loop(right, rootOp)
      case _ => true
    }

    this match {
      case HPBinOp(op, left, right) => loop(left, op) && loop(right, op)
      case _ => true
    }
  }

  /**
   * disassemble this expression by table
   *
   * This method expects [[isSimpleExpr == true]].
   * If false, this method does not do anything.
   *
   * @param exprs : table
   * @return return._1 => disassembled expressions
   *         return._2 => remain expression
   */
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

  private def purge(expr: HPExpr): Either[Unit, Option[HPExpr]] = {
    def purging(e0: HPExpr, e1: HPExpr): Either[Unit, Option[HPExpr]] = (e0, e1) match {
      case (HPBinOp(op0, _, _), HPBinOp(op1, _, _)) if op0 != op1 => Left(())
      case (HPBinOp(op, left0, right0: Ident), e1 @ HPBinOp(_, left1, right1: Ident)) =>
        if(right0.symbol == right1.symbol) purging(left0, left1) match {
          case Left(()) => Left(())
          case Right(None) => Right(None)
          case Right(Some(remain)) => Right(Some(remain))
        }
        else purging(left0, e1) match {
          case Left(()) => Left(())
          case Right(None) => Right(Some(right0))
          case Right(Some(left)) => Right(Some(HPBinOp(op, left, right0)))
        }
      case (HPBinOp(_, left, right: Ident), ident: Ident) =>
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

  def swap(table: Map[Symbol.HardwareParamSymbol, HPExpr]): HPExpr = {
    def loop(expr: HPExpr): HPExpr = expr match {
      case HPBinOp(op, left, right) => HPBinOp(op, loop(left), loop(right))
      case ident: Ident => table(ident.symbol.asHardwareParamSymbol)
      case lit => lit
    }

    loop(this).sort
  }
}

object HPExpr {
  /*
  def verifyHPBound(
    calledBounds: Vector[HPBoundTree],
    callerBounds: Vector[HPBoundTree],
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

    def compoundBounds(bounds: Vector[HPBoundTree]): Vector[HPBoundTree] = {
      def removeFirst[T](vec: Vector[T])(f: T => Boolean): (Vector[T], Option[T]) = {
        vec.foldLeft((Vector.empty[T], Option.empty[T])) {
          case ((returnedVec, Some(first)), elem) => (returnedVec :+ elem, Some(first))
          case ((returnedVec, None), elem) if f(elem) => (returnedVec, Some(elem))
          case ((returnedVec, None), elem) => (returnedVec :+ elem, None)
        }
      }

      bounds.foldLeft(Vector.empty[HPBoundTree]) {
        case (bounds, compoundedBound) =>
          val (remainBounds, foundBound) = removeFirst(bounds) {
            case HPBoundTree(expr, _) => expr.isSameExpr(compoundedBound.target)
          }

          foundBound match {
            case None => remainBounds :+ compoundedBound
            case Some(bound) =>
              def isRejected(c: RangeExpr): Boolean = bound.bounds.exists(_.isRestrictedThanEq(c))

              val constraints = compoundedBound.bounds.filterNot(isRejected)
              val restrictedBound = constraints.foldLeft(bound) {
                case (bound, constraint) =>
                  val (remain, _) = removeFirst(bound.bounds)(constraint.isRestrictedThanEq)
                  val newConstraints = remain :+ constraint

                  HPBoundTree(bound.target, newConstraints)
              }

              remainBounds :+ restrictedBound
          }
      }
    }

    def findBound(target: HPExpr, bounds: Vector[HPBoundTree]): Option[HPBoundTree] =
      bounds.find {
        bound => bound.target.isSameExpr(target)
      }

    def verifyBound(pairs: Vector[(HPBoundTree, Option[HPBoundTree])]): Either[Error, Unit] = {
      val results = pairs.map {
        case (calledBound, None) => Left(???) // Error represents caller argument bound does not meet called bound
        case (calledBound, Some(callerBound)) =>
          val isMeetAllBounds = calledBound.bounds.forall {
            calledConstraint => callerBound
              .bounds
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
      case HPBoundTree(target, constraints) =>
        val replacedTarget = replaceExpr(target, table)
        val replacedConstraints = constraints.map(_.map(replaceExpr(_, table)))

        HPBoundTree(replacedTarget, replacedConstraints)
    })

    val pairs = replacedCalledBounds.map { bound => (bound, findBound(bound.target, callerBounds)) }
    verifyBound(pairs)
  }
  */
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
case class InterfaceDef(name: String, hp: Vector[ValDef], tp: Vector[TypeDef], bounds: Vector[BoundTree], methods: Vector[MethodDef]) extends Definition
case class ImplementClass(target: TypeTree, hp: Vector[ValDef], tp: Vector[TypeDef], bounds: Vector[BoundTree], components: Vector[Component]) extends Definition
case class ImplementInterface(interface: TypeTree, target: TypeTree, hp: Vector[ValDef], tp: Vector[TypeDef], bounds: Vector[BoundTree], methods: Vector[MethodDef]) extends Definition
case class AlwaysDef(name: String, blk: Block) extends Component
case class MethodDef(flag: Modifier, name: String, hp: Vector[ValDef], tp: Vector[TypeDef], bounds: Vector[BoundTree], params: Vector[ValDef], retTpe: TypeTree, blk: Option[Block]) extends Component
case class ValDef(flag: Modifier, name: String, tpeTree: Option[TypeTree], expr: Option[Expression]) extends Component with BlockElem
case class StageDef(name: String, params: Vector[ValDef], retTpe: TypeTree, states: Vector[StateDef], blk: Vector[BlockElem]) extends Component
case class StateDef(name: String, blk: Block) extends Definition

case class TypeDef(name: String) extends Definition

trait ImplicitHPRange
object ImplicitHPRange {
  case object NotInit extends ImplicitHPRange
  case object Invalid extends ImplicitHPRange
  case class Range(max: Option[Int], min: Option[Int]) extends ImplicitHPRange
}

trait BoundTree extends AST
case class TPBoundTree(target: TypeTree, bounds: Vector[TypeTree]) extends BoundTree
case class HPBoundTree(target: HPExpr, bounds: Vector[RangeExpr]) extends BoundTree {
  /*
  /**
   * `this` and `that` have bounds that are already sorted.
   * if `this` or `that` is not sorted, this method may return inappropriate result
   * @param that
   * @return whether bound range is overlapped or not
   */
  def isOverlapped(that: HPBoundTree): Boolean = {
    /**
     * @param bounds target expr bounds
     * @return None:           this is invalid range for example `m > 10 && m < 0`
     *         Some(max, min): max and min are Some if it has value
     */
    def makeRange(bounds: Vector[RangeExpr]): Option[(Option[Int], Option[Int])] = {
      val max = bounds.collectFirst {
        case RangeExpr.LT(IntLiteral(value)) => value - 1
        case RangeExpr.LE(IntLiteral(value)) => value
      }

      val min = bounds.collectFirst {
        case RangeExpr.GT(IntLiteral(value)) => value + 1
        case RangeExpr.GE(IntLiteral(value)) => value
      }

      (max, min) match {
        case (Some(max), Some(min)) if max >= min => Some(Some(max), Some(min))
        case (Some(_), Some(_))                   => None
        case (None, None)                         => Some(None, None)
        case (max, min)                           => Some(max, min)
      }
    }

    val thisRange = makeRange(this.bounds)
    val thatRange = makeRange(that.bounds)

    (thisRange, thatRange) match {
      case (None, _) => false
      case (_, None) => false
      case (Some((thisMax, thisMin)), Some((thatMax, thatMin))) =>
        // less than equal
        def le(left: Option[Int], right: Option[Int]): Boolean =
          (left, right) match {
            case (None, _) => true
            case (_, None) => true
            case (Some(left), Some(right)) => left <= right
          }

        le(thisMin, thatMax) && le(thatMin, thisMax)
    }
  }
   */

  /*
  def compound(): HPBoundTree = {
    def loop(bounds: Vector[RangeExpr]): Vector[RangeExpr] = {
      bounds match {
        case Vector() => Vector.empty
        case bounds =>
          val (restricted, remains) = bounds.tail.foldLeft((bounds.head, Vector.empty[RangeExpr])) {
            case ((bound, others), subject) => bound.compound(subject) match {
              case Some(newBound) => (newBound, others)
              case None => (bound, others :+ subject)
            }
          }

          restricted +: loop(remains)
      }
    }

    HPBoundTree(this.target, loop(this.bounds))
  }
 */
}

object HPBoundTree {
  /**
   * make implicit hardware parameter bounds in explicit
   *
   * E.g.
   *   where m : gt n          ==> where m : gt n & gt 1
   *         n : gt 0                    n : gt 0
   *
   *   where l : gt m + n      ==> where l : gt m + n & gt 7
   *         m : gt 3                    m : gt 3
   *         n : gt 2                    n : gt 2
   *
   *   where     l : gt m + n  ==> where     l : gt m + n & gt 11
   *             m : gt 3                    m : gt 3
   *             n : gt 2                    n : gt 2
   *         m + n : gt 10               m + n : gt 10
   *
   * Note:
   *   If there are cyclic references, this method raises ImplementationErrorException.
   *
   * param hpBounds
   * return hardware parameter bounds that are made all implicit bounds in explicit
   */
    /*
  def makeImplicitRestrictionExplicit(hpBounds: Vector[HPBoundTree]): Vector[HPBoundTree] = {
    def sortByTarget: Vector[HPBoundTree] = {
      def collectLeafHash(expr: HPExpr): Vector[Int] =
        expr match {
          case HPBinOp(_, left, right) => collectLeafHash(left) ++ collectLeafHash(right)
          case leaf => Vector(leaf.hashCode)
        }

      val sortedByAsc = hpBounds.sortWith {
        case (b0, b1) =>
          val hashes0 = collectLeafHash(b0.target)
          val hashes1 = collectLeafHash(b1.target)

          if(hashes0.length != hashes1.length) hashes0.length < hashes1.length
          else {
            val diff = hashes0.zip(hashes1).find { case (h0, h1) => h0 != h1 }
            diff match {
              case Some((h0, h1)) => h0 < h1
              case None => false
            }
          }
      }

      sortedByAsc.reverse
    }

    def initCacheTable: Vector[(HPExpr, ImplicitHPRange)] = {
      hpBounds.flatMap {
        case HPBoundTree(target: Ident, bounds) =>
          val existsExprBound = bounds.exists(_.expr match {
            case _: IntLiteral => false
            case _ => true
          })

          if(existsExprBound) None
          else {
            val min = bounds.collectFirst {
              case RangeExpr.GE(IntLiteral(value)) => value
              case RangeExpr.GT(IntLiteral(value)) => value + 1
            }

            val max = bounds.collectFirst {
              case RangeExpr.LE(IntLiteral(value)) => value
              case RangeExpr.LT(IntLiteral(value)) => value + 1
            }

            val range = (max, min) match {
              case (max @ Some(v0), min @ Some(v1)) =>
                if(v0 >= v1)ImplicitHPRange.Range(max, min)
                else ImplicitHPRange.Invalid
              case (max, min) => ImplicitHPRange.Range(max, min)
            }

            Some(target, range)
          }
        case _ => None
      }
    }

    val table = initCacheTable
  }
   */
}

trait RangeExpr {
  val expr: HPExpr
  /*
  def isRestrictedThanEq(that: RangeExpr): Boolean = {
    import RangeExpr._

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
   */

  /*
  def compound(that: RangeExpr): Option[RangeExpr] =
    if(this.isRestrictedThanEq(that)) Some(this)
    else if(that.isRestrictedThanEq(this)) Some(that)
    else None
  */

  def map(f: HPExpr => HPExpr): RangeExpr = {
    this match {
      case RangeExpr.EQ(expr) => RangeExpr.EQ(f(expr))
      case RangeExpr.NE(expr) => RangeExpr.NE(f(expr))
      case RangeExpr.Min(expr) => RangeExpr.Min(f(expr))
      case RangeExpr.Max(expr) => RangeExpr.Max(f(expr))
    }
  }
}
object RangeExpr {
  case class EQ(expr: HPExpr) extends RangeExpr
  case class NE(expr: HPExpr) extends RangeExpr
  case class Min(expr: HPExpr) extends RangeExpr
  case class Max(expr: HPExpr) extends RangeExpr
}

case class Ident(name: String) extends Expression with TypeAST with HasSymbol with HPExpr
case class Apply(prefix: Expression, hps: Vector[HPExpr], tps: Vector[TypeTree], args: Vector[Expression]) extends Expression

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
  op: Operation,
  left: Expression with HPExpr,
  right: Expression with HPExpr
) extends BinOp with HPExpr {
  type Expr = Expression with HPExpr
}

case class Select(prefix: Expression, name: String) extends Expression with HasSymbol
case class StaticSelect(suffix: TypeTree, name: String) extends Expression with TypeAST
case class Block(elems: Vector[BlockElem], last: Expression) extends Expression
case class Construct(name: TypeTree, pairs: Vector[ConstructPair]) extends Expression
case class ConstructPair(name: String, expr: Expression) extends AST
case class This() extends Expression
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
case class TypeTree(expr: Ident, hp: Vector[HPExpr], tp: Vector[TypeTree]) extends AST with HasType with HasSymbol
case class ThisType() extends TypeAST

trait Operation {
  def toInterface: String
  def toMethod: String = this.toInterface.toLowerCase
  def toOperator: String
  def isCommutative: Boolean
}
object Operation {
  case object Add extends Operation {
    override def toInterface: String = "Add"
    override def toOperator: String = "+"
    override def isCommutative: Boolean = true
  }

  case object Sub extends Operation {
    override def toInterface: String = "Sub"
    override def toOperator: String = "-"
    override def isCommutative: Boolean = false
  }

  case object Mul extends Operation {
    override def toInterface: String = "Mul"
    override def toOperator: String = "*"
    override def isCommutative: Boolean = true
  }

  case object Div extends Operation {
    override def toInterface: String = "Div"
    override def toOperator: String = "/"
    override def isCommutative: Boolean = false
  }
}