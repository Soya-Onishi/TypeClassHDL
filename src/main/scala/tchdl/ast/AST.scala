package tchdl.ast

import tchdl.parser.Filename
import tchdl.util.TchdlException.ImplementationErrorException
import tchdl.util._

sealed trait AST {
  var _id = TreeID.id()
  def id: Int = this._id
  def setID(id: Int): this.type = { this._id = id; this }

  val position: Position
}

object TreeID {
  var _id: Int = 0
  def id(): Int = {
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
      def reConstruct(leafs: Vector[HPExpr]): HPExpr = {
        val binop = leafs.reduceRight[HPExpr]{
          case (expr, leaf) =>
            val start = expr.position.start
            val end = leaf.position.end
            val pos = Position(expr.position.filename, start, end)

            HPBinOp(expr, leaf, pos)
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

      reConstruct(sortedLeafs)
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

    def reConstruct(leafs: Vector[HPExpr]): HPExpr = leafs match {
      case Vector(leaf) => leaf
      case leafs =>
        val left = reConstruct(leafs.init)
        val pos = Position(left, leafs.last)
        HPBinOp(left, leafs.last, pos)
    }

    def exec(binop: HPBinOp): HPExpr = {
      val leafs = collectLeafs(binop)
      val lits = leafs.collect { case lit: IntLiteral => lit }
      val others = leafs.filterNot(_.isInstanceOf[IntLiteral])

      if(lits.isEmpty) binop
      else {
        val litStart = others.lastOption.getOrElse(binop).position.start
        val litEnd = lits.last.position.end
        val litPos = Position(binop.position.filename, litStart, litEnd)
        val nums = lits.map(_.value)

        val combined = IntLiteral(nums.reduce[Int]{ case (l, r) => calc(binop.op, l, r) }, litPos)
        reConstruct(others :+ combined)
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
      case bin @ HPBinOp(left, right) => bin.copy(left = loop(left), right = loop(right))
      case ident: Ident => hpTable.getOrElse(ident.symbol.asHardwareParamSymbol, ident)
      case e => e
    }

    loop(this).sort
  }

  def swap(table: Map[Symbol.HardwareParamSymbol, HPExpr]): HPExpr = {
    def loop(expr: HPExpr): HPExpr = expr match {
      case bin @ HPBinOp(left, right) => bin.copy(left = loop(left), right = loop(right))
      case ident: Ident => table(ident.symbol.asHardwareParamSymbol)
      case lit => lit
    }

    loop(this).sort
  }

  def extractConstant:(HPExpr, Option[IntLiteral]) = this.sort.combine match {
    case HPBinOp(left, right: IntLiteral) => (left, Some(right))
    case expr => (expr, None)
  }

  def negate: HPExpr = this match {
    case bin @ HPBinOp(left, right) => HPBinOp(left.negate, right.negate, bin.position)
    case ident: Ident => HPUnaryOp(ident, ident.position)
    case HPUnaryOp(ident) => ident
    case int @ IntLiteral(value) => IntLiteral(-value, int.position)
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
  protected var _tpe: Option[Type] = None
  def tpe: Type = _tpe.get
  def setTpe(tpe: Type): this.type = { _tpe = Some(tpe); this }
}

trait HasSymbol {
  protected var _symbol: Option[Symbol] = None
  def symbol: Symbol = _symbol.get
  def setSymbol(symbol: Symbol): this.type = { _symbol = Some(symbol); this }
}

abstract case class CompilationUnit private (filename: String, pkgName: Vector[String], imports: Vector[Vector[String]], topDefs: Vector[Definition]) extends AST {
  override def toString: String = s"CU[$filename, ${pkgName.mkString("::")}]"
  def copy(
    filename: String = this.filename,
    pkgName: Vector[String] = this.pkgName,
    imports: Vector[Vector[String]] = this.imports,
    topDefs: Vector[Definition] = this.topDefs
  ): CompilationUnit = {
    val oldPos = this.position
    val oldID = this._id

    new CompilationUnit(filename, pkgName, imports, topDefs) {
      override val position = oldPos
      this._id = oldID
    }
  }
}

object CompilationUnit {
  def apply(filename: String, pkgName: Vector[String], imports: Vector[Vector[String]], topDefs: Vector[Definition], pos: Position): CompilationUnit = {
    new CompilationUnit(filename, pkgName, imports, topDefs) {
      override val position = pos
    }
  }
}

abstract case class ModuleDef private (name: String, hp: Vector[ValDef], tp: Vector[TypeDef], bounds: Vector[BoundTree], parents: Vector[ValDef], siblings: Vector[ValDef]) extends Definition {
  def copy(
    name: String = this.name,
    hp: Vector[ValDef] = this.hp,
    tp: Vector[TypeDef] = this.tp,
    bounds: Vector[BoundTree] = this.bounds,
    parents: Vector[ValDef] = this.parents,
    siblings: Vector[ValDef] = this.siblings
  ): ModuleDef = {
    val oldPos = this.position
    val oldID = this._id
    val oldSym = this._symbol

    new ModuleDef(name, hp, tp, bounds, parents, siblings) {
      override val position = oldPos
      this._id = oldID
      this._symbol = oldSym
    }
  }
}

object ModuleDef {
  def apply(name: String, hp: Vector[ValDef], tp: Vector[TypeDef], bounds: Vector[BoundTree], parents: Vector[ValDef], siblings: Vector[ValDef], pos: Position): ModuleDef = {
    new ModuleDef(name, hp, tp, bounds, parents, siblings) {
      override val position = pos
    }
  }
}

abstract case class StructDef private (name: String, hp: Vector[ValDef], tp: Vector[TypeDef], bounds: Vector[BoundTree], fields: Vector[ValDef]) extends Definition {
  def copy(
    name: String = this.name,
    hp: Vector[ValDef] = this.hp,
    tp: Vector[TypeDef] = this.tp,
    bounds: Vector[BoundTree] = this.bounds,
    fields: Vector[ValDef] = this.fields
  ): StructDef = {
    val oldPos = this.position
    val oldID = this._id
    val oldSym = this._symbol

    new StructDef(name, hp, tp, bounds, fields) {
      override val position = oldPos
      this._id = oldID
      this._symbol = oldSym
    }
  }
}

object StructDef {
  def apply(name: String, hp: Vector[ValDef], tp: Vector[TypeDef], bounds: Vector[BoundTree], fields: Vector[ValDef], pos: Position): StructDef = {
    new StructDef(name, hp, tp, bounds, fields) {
      override val position = pos
    }
  }
}

abstract case class InterfaceDef private (flag: Modifier, name: String, hp: Vector[ValDef], tp: Vector[TypeDef], bounds: Vector[BoundTree], methods: Vector[MethodDef], types: Vector[TypeDef]) extends Definition {
  def copy(
    flag: Modifier = this.flag,
    name: String = this.name,
    hp: Vector[ValDef] = this.hp,
    tp: Vector[TypeDef] = this.tp,
    bounds: Vector[BoundTree] = this.bounds,
    methods: Vector[MethodDef] = this.methods,
    types: Vector[TypeDef] = this.types
  ): InterfaceDef = {
    val oldPos = this.position
    val oldID = this._id
    val oldSym = this._symbol

    new InterfaceDef(flag, name, hp, tp, bounds, methods, types) {
      override val position = oldPos
      this._id = oldID
      this._symbol = oldSym
    }
  }
}

object InterfaceDef {
  def apply(flag: Modifier, name: String, hp: Vector[ValDef], tp: Vector[TypeDef], bounds: Vector[BoundTree], methods: Vector[MethodDef], typed: Vector[TypeDef], pos: Position): InterfaceDef = {
    new InterfaceDef(flag, name, hp, tp, bounds, methods, typed) {
      override val position = pos
    }
  }
}

abstract case class EnumDef private (name: String, hp: Vector[ValDef], tp: Vector[TypeDef], bounds: Vector[BoundTree], members: Vector[EnumMemberDef]) extends Definition {
  def copy(
    name: String = this.name,
    hp: Vector[ValDef] = this.hp,
    tp: Vector[TypeDef] = this.tp,
    bounds: Vector[BoundTree] = this.bounds,
    members: Vector[EnumMemberDef] = this.members
  ): EnumDef = {
    val pos = this.position
    val oldID = this._id
    val sym = this._symbol

    new EnumDef(name, hp, tp, bounds, members) {
      override val position = pos
      this._id = oldID
      this._symbol = sym
    }
  }
}

object EnumDef {
  def apply(name: String, hp: Vector[ValDef], tp: Vector[TypeDef], bounds: Vector[BoundTree], members: Vector[EnumMemberDef], pos: Position): EnumDef = {
    new EnumDef(name, hp, tp, bounds, members) {
      override val position = pos
    }
  }
}

abstract case class EnumMemberDef private (name: String, fields: Vector[TypeTree], member: Option[BigInt]) extends Definition {
  def copy(name: String = this.name, fields: Vector[TypeTree] = this.fields, member: Option[BigInt] = this.member): EnumMemberDef = {
    val pos = this.position
    val sym = this._symbol
    val oldId = this._id

    new EnumMemberDef(name, fields, member) {
      override val position = pos
      _id = oldId
      _symbol = sym
    }
  }
}

object EnumMemberDef {
  def apply(name: String, fields: Vector[TypeTree], member: Option[BigInt], pos: Position): EnumMemberDef = {
    new EnumMemberDef(name, fields, member) {
      override val position = pos
    }
  }
}

abstract case class ImplementClass private (target: TypeTree, hp: Vector[ValDef], tp: Vector[TypeDef], bounds: Vector[BoundTree], components: Vector[Component]) extends Definition {
  def copy(
    target: TypeTree = this.target,
    hp: Vector[ValDef] = this.hp,
    tp: Vector[TypeDef] = this.tp,
    bounds: Vector[BoundTree] = this.bounds,
    components: Vector[Component] = this.components
  ): ImplementClass = {
    val pos = this.position
    val sym = this._symbol
    val oldId = this._id

    new ImplementClass(target, hp, tp, bounds, components) {
      override val position = pos
      _symbol = sym
      _id = oldId
    }
  }
}

object ImplementClass {
  def apply(target: TypeTree, hp: Vector[ValDef], tp: Vector[TypeDef], bounds: Vector[BoundTree], components: Vector[Component], pos: Position): ImplementClass = {
    new ImplementClass(target, hp, tp, bounds, components) {
      override val position = pos
    }
  }
}

abstract case class ImplementInterface private (interface: TypeTree, target: TypeTree, hp: Vector[ValDef], tp: Vector[TypeDef], bounds: Vector[BoundTree], methods: Vector[MethodDef], types: Vector[TypeDef]) extends Definition {
  def copy(
    interface: TypeTree = this.interface,
    target: TypeTree = this.target,
    hp: Vector[ValDef] = this.hp,
    tp: Vector[TypeDef] = this.tp,
    bounds: Vector[BoundTree] = this.bounds,
    methods: Vector[MethodDef] = this.methods,
    types: Vector[TypeDef] = this.types
  ): ImplementInterface = {
    val pos = this.position
    val sym = this._symbol
    val oldID = this._id

    new ImplementInterface(interface, target, hp, tp, bounds, methods, types) {
      override val position = pos
      _symbol = sym
      _id = oldID
    }
  }
}

object ImplementInterface {
  def apply(interface: TypeTree, target: TypeTree, hp: Vector[ValDef], tp: Vector[TypeDef], bounds: Vector[BoundTree], methods: Vector[MethodDef], types: Vector[TypeDef], pos: Position): ImplementInterface = {
    new ImplementInterface(interface, target, hp, tp, bounds, methods, types) {
      override val position = pos
    }
  }
}

abstract case class AlwaysDef private (name: String, blk: Block) extends Component {
  def copy(name: String = this.name, blk: Block = this.blk): AlwaysDef = {
    val pos = this.position
    val sym = this._symbol
    val oldID = this._id

    new AlwaysDef(name, blk) {
      override val position = pos
      _symbol = sym
      _id = oldID
    }
  }
}

object AlwaysDef {
  def apply(name: String, blk: Block, pos: Position): AlwaysDef = {
    new AlwaysDef(name, blk) {
      override val position = pos
    }
  }
}

abstract case class ProcDef private (name: String, retTpe: TypeTree, default: Expression, blks: Vector[ProcBlock]) extends Component {
  def copy(name: String = this.name, retTpe: TypeTree = this.retTpe, default: Expression = this.default, blks: Vector[ProcBlock] = this.blks): ProcDef = {
    val pos = this.position
    val sym = this._symbol
    val oldID = this._id

    new ProcDef(name, retTpe, default, blks) {
      override val position = pos
      _symbol = sym
      _id = oldID
    }
  }
}

object ProcDef {
  def apply(name: String, retTpe: TypeTree, default: Expression, blks: Vector[ProcBlock], pos: Position): ProcDef = {
    new ProcDef(name, retTpe, default, blks) {
      override val position = pos
    }
  }
}

abstract case class ProcBlock private(modifier: Modifier, name: String, params: Vector[ValDef], blk: Block) extends Definition {
  def copy(modifier: Modifier = this.modifier, name: String = this.name, params: Vector[ValDef] = this.params, blk: Block = this.blk): ProcBlock = {
    val pos = this.position
    val sym = this._symbol
    val oldID = this._id

    new ProcBlock(modifier, name, params, blk) {
      override val position = pos
      _symbol = sym
      _id = oldID
    }
  }
}

object ProcBlock {
  def apply(modifier: Modifier, name: String, params: Vector[ValDef], blk: Block, pos: Position): ProcBlock = {
    new ProcBlock(modifier, name, params, blk) {
      override val position = pos
    }
  }
}

abstract case class MethodDef private (annons: Vector[Annotation], flag: Modifier, name: String, hp: Vector[ValDef], tp: Vector[TypeDef], bounds: Vector[BoundTree], params: Vector[ValDef], retTpe: TypeTree, blk: Option[Block]) extends Component {
  def copy(
    annons: Vector[Annotation] = this.annons,
    flag: Modifier = this.flag,
    name: String = this.name,
    hp: Vector[ValDef] = this.hp,
    tp: Vector[TypeDef] = this.tp,
    bounds: Vector[BoundTree] = this.bounds,
    params: Vector[ValDef] = this.params,
    retTpe: TypeTree = this.retTpe,
    blk: Option[Block] = this.blk
  ): MethodDef = {
    val pos = this.position
    val sym = this._symbol
    val oldID = this._id

    new MethodDef(annons, flag, name, hp, tp, bounds, params, retTpe, blk) {
      override val position = pos
      _symbol = sym
      _id = oldID
    }
  }
}

object MethodDef {
  def apply(annons: Vector[Annotation], flag: Modifier, name: String, hp: Vector[ValDef], tp: Vector[TypeDef], bounds: Vector[BoundTree], params: Vector[ValDef], retTpe: TypeTree, blk: Option[Block], pos: Position): MethodDef = {
    new MethodDef(annons, flag, name, hp, tp, bounds, params, retTpe, blk) {
      override val position = pos
    }
  }
}

abstract case class ValDef private (flag: Modifier, name: String, tpeTree: Option[TypeTree], expr: Option[Expression]) extends Component with BlockElem {
  def copy(
    flag: Modifier = this.flag,
    name: String = this.name,
    tpeTree: Option[TypeTree] = this.tpeTree,
    expr: Option[Expression] = this.expr
  ): ValDef = {
    val pos = this.position
    val sym = this._symbol
    val oldID = this._id

    new ValDef(flag, name, tpeTree, expr) {
      override val position = pos
      _symbol = sym
      _id = oldID
    }
  }
}

object ValDef {
  def apply(flag: Modifier, name: String, tpeTree: Option[TypeTree], expr: Option[Expression], pos: Position): ValDef = {
    new ValDef(flag, name, tpeTree, expr) {
      override val position = pos
    }
  }
}

abstract case class StageDef private (name: String, params: Vector[ValDef], states: Vector[StateDef], blk: Vector[BlockElem]) extends Component {
  def copy(
    name: String = this.name,
    params: Vector[ValDef] = this.params,
    states: Vector[StateDef] = this.states,
    blk: Vector[BlockElem] = this.blk
  ): StageDef = {
    val pos = this.position
    val sym = this._symbol
    val oldID = this._id

    new StageDef(name, params, states, blk) {
      override val position = pos
      _symbol = sym
      _id = oldID
    }
  }
}

object StageDef {
  def apply(name: String, params: Vector[ValDef], states: Vector[StateDef], blk: Vector[BlockElem], pos: Position): StageDef = {
    new StageDef(name, params, states, blk) {
      override val position = pos
    }
  }
}

abstract case class StateDef private (name: String, params: Vector[ValDef], blk: Block) extends Definition {
  def copy(
    name: String = this.name,
    params: Vector[ValDef] = this.params,
    blk: Block = this.blk
  ): StateDef = {
    val pos = this.position
    val sym = this._symbol
    val oldID = this._id

    new StateDef(name, params, blk) {
      override val position = pos
      _symbol = sym
      _id = oldID
    }
  }
}

object StateDef {
  def apply(name: String, params: Vector[ValDef], blk: Block, pos: Position): StateDef = {
    new StateDef(name, params, blk) {
      override val position = pos
    }
  }
}

abstract case class TypeDef private (flag: Modifier, name: String, tpe: Option[TypeTree]) extends Definition {
  def copy(
    flag: Modifier = this.flag,
    name: String = this.name,
    tpe: Option[TypeTree] = this.tpe
  ): TypeDef = {
    val pos = this.position
    val sym = this._symbol
    val oldID = this._id

    new TypeDef(flag, name, tpe) {
      override val position = pos
      _symbol = sym
      _id = oldID
    }
  }
}

object TypeDef {
  def apply(flag: Modifier, name: String, tpe: Option[TypeTree], pos: Position): TypeDef = {
    new TypeDef(flag, name, tpe) {
      override val position = pos
    }
  }
}

sealed trait BoundTree extends AST
abstract case class TPBoundTree private (target: TypeTree, bounds: Vector[TypeTree]) extends BoundTree {
  def copy(target: TypeTree = this.target, bounds: Vector[TypeTree] = this.bounds): TPBoundTree = {
    val pos = this.position
    val oldID = this._id

    new TPBoundTree(target, bounds) {
      override val position = pos
      _id = oldID
    }
  }
}

object TPBoundTree {
  def apply(target: TypeTree, bounds: Vector[TypeTree], pos: Position): TPBoundTree = {
    new TPBoundTree(target, bounds) {
      override val position = pos
    }
  }
}

abstract case class HPBoundTree private (target: HPExpr, bounds: Vector[RangeExpr]) extends BoundTree {
  def copy(target: HPExpr = this.target, bounds: Vector[RangeExpr] = this.bounds): HPBoundTree = {
    val pos = this.position
    val oldID = this._id

    new HPBoundTree(target, bounds) {
      override val position = pos
      _id = oldID
    }
  }
}

object HPBoundTree {
  def apply(target: HPExpr, bounds: Vector[RangeExpr], pos: Position): HPBoundTree = {
    new HPBoundTree(target, bounds) {
      override val position = pos
    }
  }
}

sealed trait RangeExpr { val expr: HPExpr }
object RangeExpr {
  case class EQ(expr: HPExpr) extends RangeExpr
  case class Min(expr: HPExpr) extends RangeExpr
  case class Max(expr: HPExpr) extends RangeExpr
}

abstract case class Ident private (name: String) extends Expression with TypeAST with HasSymbol with HPExpr with ApplyPrefix {
  def copy(name: String = this.name): Ident = {
    val pos = this.position
    val oldTpe = this._tpe
    val oldSym = this._symbol
    val oldID = this._id
    val oldSort = this._sortedExpr

    new Ident(name) {
      override val position = pos
      this._tpe = oldTpe
      this._symbol = oldSym
      this._id = oldID
      this._sortedExpr = oldSort
    }
  }
}

object Ident {
  def apply(name: String, pos: Position): Ident = {
    new Ident(name) {
      override val position = pos
    }
  }
}

abstract case class Apply private (prefix: ApplyPrefix, hps: Vector[HPExpr], tps: Vector[TypeTree], args: Vector[Expression]) extends Expression {
  def copy(
    prefix: ApplyPrefix,
    hps: Vector[HPExpr],
    tps: Vector[TypeTree],
    args: Vector[Expression]
  ): Apply = {
    val oldPos = this.position
    val oldID = this._id
    val oldTpe = this._tpe

    new Apply(prefix, hps, tps, args) {
      override val position = oldPos
      this._id = oldID
      this._tpe = oldTpe
    }
  }
}

object Apply {
  def apply(prefix: ApplyPrefix, hps: Vector[HPExpr], tps: Vector[TypeTree], args: Vector[Expression], pos: Position): Apply = {
    new Apply(prefix, hps, tps, args) {
      override val position = pos
    }
  }
}


abstract case class Select private (prefix: Expression, name: String) extends Expression with HasSymbol with ApplyPrefix {
  def copy(prefix: Expression = this.prefix, name: String = this.name): Select = {
    val oldPos = this.position
    val oldID = this._id
    val oldSym = this._symbol
    val oldTpe = this._tpe

    new Select(prefix, name) {
      override val position = oldPos
      this._id = oldID
      this._symbol = oldSym
      this._tpe = oldTpe
    }
  }
}

object Select {
  def apply(prefix: Expression, name: String, pos: Position): Select = {
    new Select(prefix, name) {
      override val position = pos
    }
  }
}

abstract case class StaticSelect private (prefix: TypeTree, name: String) extends Expression with TypeAST with ApplyPrefix {
  def copy(prefix: TypeTree = this.prefix, name: String = this.name): StaticSelect = {
    val oldPos = this.position
    val oldTpe = this._tpe
    val oldSymbol = this._symbol
    val oldID = this._id

    new StaticSelect(prefix, name) {
      override val position = oldPos
      this._tpe = oldTpe
      this._symbol = oldSymbol
      this._id = oldID
    }
  }
}

object StaticSelect {
  def apply(prefix: TypeTree, name: String, pos: Position): StaticSelect = {
    new StaticSelect(prefix, name) {
      override val position = pos
    }
  }
}

abstract case class CastExpr private (expr: Expression, to: TypeTree) extends Expression {
  def copy(expr: Expression = this.expr, to: TypeTree = this.to): CastExpr = {
    val oldPos = this.position
    val oldTpe = this._tpe
    val oldID = this._id

    new CastExpr(expr, to) {
      override val position = oldPos
      this._tpe = oldTpe
      this._id = oldID
    }
  }
}

object CastExpr {
  def apply(expr: Expression, to: TypeTree, pos: Position): CastExpr = {
    new CastExpr(expr, to) {
      override val position = pos
    }
  }
}

abstract case class SelectPackage private (packages: Vector[String], name: String) extends AST with TypeAST with Expression {
  def copy(
    packages: Vector[String] = this.packages,
    name: String = this.name
  ): SelectPackage = {
    val oldPos = this.position
    val oldID = this._id
    val oldSym = this._symbol
    val oldTpe = this._tpe

    new SelectPackage(packages, name) {
      override val position = oldPos
      this._id = oldID
      this._symbol = oldSym
      this._tpe = oldTpe
    }
  }
}

object SelectPackage {
  def apply(packages: Vector[String], name: String, pos: Position): SelectPackage = {
    new SelectPackage(packages, name) {
      override val position = pos
    }
  }
}

abstract case class Block private (elems: Vector[BlockElem], last: Expression) extends Expression {
  def copy(elems: Vector[BlockElem] = this.elems, last: Expression = this.last): Block = {
    val oldPos = this.position
    val oldID = this._id
    val oldTpe = this._tpe

    new Block(elems, last) {
      override val position = oldPos
      this._id = oldID
      this._tpe = oldTpe
    }
  }
}

object Block {
  def apply(elems: Vector[BlockElem], last: Expression, pos: Position): Block = {
    new Block(elems, last) {
      override val position = pos
    }
  }
}

abstract case class ConstructClass private (target: TypeTree, fields: Vector[ConstructPair]) extends Construct {
  def copy(target: TypeTree = this.target, fields: Vector[ConstructPair] = this.fields): ConstructClass = {
    val oldPos = this.position
    val oldID = this._id
    val oldSym = this._symbol
    val oldTpe = this._tpe

    new ConstructClass(target, fields) {
      override val position = oldPos
      this._id = oldID
      this._symbol = oldSym
      this._tpe = oldTpe
    }
  }
}

object ConstructClass {
  def apply(target: TypeTree, fields: Vector[ConstructPair], pos: Position): ConstructClass = {
    new ConstructClass(target, fields) {
      override val position = pos
    }
  }
}

abstract case class ConstructModule private (target: TypeTree, parents: Vector[ConstructPair], siblings: Vector[ConstructPair]) extends Construct {
  def copy(target: TypeTree = this.target, parents: Vector[ConstructPair] = this.parents, siblings: Vector[ConstructPair] = this.siblings): ConstructModule = {
    val oldPos = this.position
    val oldTpe = this._tpe
    val oldSym = this._symbol
    val oldID = this._id

    new ConstructModule(target, parents, siblings) {
      override val position = oldPos
      this._tpe = oldTpe
      this._symbol = oldSym
      this._id = oldID
    }
  }
}

object ConstructModule {
  def apply(target: TypeTree, parents: Vector[ConstructPair], siblings: Vector[ConstructPair], pos: Position): ConstructModule = {
    new ConstructModule(target, parents, siblings) {
      override val position = pos
    }
  }
}

abstract case class ConstructEnum private (target: TypeTree, fields: Vector[Expression]) extends Construct {
  def copy(target: TypeTree = this.target, fields: Vector[Expression] = this.fields): ConstructEnum = {
    val oldPos = this.position
    val oldID = this._id
    val oldSym = this._symbol
    val oldTpe = this._tpe

    new ConstructEnum(target, fields) {
      override val position = oldPos
      this._id = oldID
      this._symbol = oldSym
      this._tpe = oldTpe
    }
  }
}

object ConstructEnum {
  def apply(target: TypeTree, fields: Vector[Expression], pos: Position): ConstructEnum = {
    new ConstructEnum(target, fields) {
      override val position = pos
    }
  }
}

abstract case class ConstructPair private (name: String, init: Expression) extends AST {
  def copy(name: String = this.name, init: Expression = this.init): ConstructPair = {
    val oldPos = this.position
    val oldID = this._id

    new ConstructPair(name, init) {
      override val position = oldPos
      this._id = oldID
    }
  }
}

object ConstructPair {
  def apply(name: String, init: Expression, pos: Position): ConstructPair = {
    new ConstructPair(name, init) {
      override val position = pos
    }
  }
}

abstract case class Assign private (left: Expression, right: Expression) extends BlockElem {
  def copy(left: Expression = this.left, right: Expression = this.right): Assign = {
    val oldPos = this.position
    val oldID = this._id

    new Assign(left, right) {
      override val position = oldPos
      this._id = oldID
    }
  }
}

object Assign {
  def apply(left: Expression, right: Expression, pos: Position): Assign = {
    new Assign(left, right) {
      override val position = pos
    }
  }
}

abstract case class This private () extends Expression {
  def copy(): This = {
    val oldPos = this.position
    val oldID = this._id
    val oldTpe = this._tpe

    new This() {
      override val position = oldPos
      this._id = oldID
      this._tpe = oldTpe
    }
  }
}

object This {
  def apply(pos: Position): This = {
    new This() {
      override val position = pos
    }
  }
}

abstract case class IfExpr private (cond: Expression, conseq: Expression, alt: Option[Expression]) extends Expression {
  def copy(cond: Expression = this.cond, conseq: Expression = this.conseq, alt: Option[Expression] = this.alt): IfExpr = {
    val oldPos = this.position
    val oldID = this._id
    val oldTpe = this._tpe

    new IfExpr(cond, conseq, alt) {
      override val position = oldPos
      this._id = oldID
      this._tpe = oldTpe
    }
  }
}

object IfExpr {
  def apply(cond: Expression, conseq: Expression, alt: Option[Expression], pos: Position): IfExpr = {
    new IfExpr(cond, conseq, alt) {
      override val position = pos
    }
  }
}

abstract case class BitLiteral private (value: BigInt, length: Int) extends Literal {
  def copy(value: BigInt = this.value, length: Int = this.length): BitLiteral = {
    val oldPos = this.position
    val oldID = this._id
    val oldTpe = this._tpe

    new BitLiteral(value, length) {
      override val position = oldPos
      this._id = oldID
      this._tpe = oldTpe
    }
  }
}

object BitLiteral {
  def apply(value: BigInt, length: Int, pos: Position): BitLiteral = {
    new BitLiteral(value, length) {
      override val position = pos
    }
  }
}

abstract case class IntLiteral private (value: Int) extends Literal with HPExpr {
  def copy(value: Int = this.value): IntLiteral = {
    val oldPos = this.position
    val oldID = this._id
    val oldTpe = this._tpe
    val oldExpr = this._sortedExpr

    new IntLiteral(value) {
      override val position = oldPos
      this._id = oldID
      this._tpe = oldTpe
      this._sortedExpr = oldExpr
    }
  }
}

object IntLiteral {
  def apply(value: Int, pos: Position): IntLiteral = {
    new IntLiteral(value) {
      override val position = pos
    }
  }
}

abstract case class BoolLiteral private (value: Boolean) extends Literal with HPExpr {
  def copy(value: Boolean = this.value): BoolLiteral = {
    val oldPos = this.position
    val oldID = this._id
    val oldTpe = this._tpe
    val oldExpr = this._sortedExpr

    new BoolLiteral(value) {
      override val position = oldPos
      this._id = oldID
      this._tpe = oldTpe
      this._sortedExpr = oldExpr
    }
  }
}

object BoolLiteral {
  def apply(value: Boolean, pos: Position): BoolLiteral = {
    new BoolLiteral(value) {
      override val position = pos
    }
  }
}

abstract case class UnitLiteral private () extends Literal {
  def copy(): UnitLiteral = {
    val oldPos = this.position
    val oldID = this._id
    val oldTpe = this._tpe

    new UnitLiteral {
      override val position = oldPos
      this._id = oldID
      this._tpe = oldTpe
    }
  }
}

object UnitLiteral {
  def apply(pos: Position): UnitLiteral = {
    new UnitLiteral {
      override val position = pos
    }
  }
}

abstract case class StringLiteral private (str: String) extends Literal with HPExpr {
  def copy(str: String = this.str): StringLiteral = {
    val oldPos = this.position
    val oldID = this._id
    val oldTpe = this._tpe
    val oldExpr = this._sortedExpr

    new StringLiteral(str) {
      override val position = oldPos
      this._id = oldID
      this._tpe = oldTpe
      this._sortedExpr = oldExpr
    }
  }
}

object StringLiteral {
  def apply(str: String, pos: Position): StringLiteral = {
    new StringLiteral(str) {
      override val position = pos
    }
  }
}

abstract case class Finish private () extends Expression {
  def copy(): Finish = {
    val oldPos = this.position
    val oldID = this._id
    val oldTpe = this._tpe

    new Finish {
      override val position = oldPos
      this._id = oldID
      this._tpe = oldTpe
    }
  }
}

object Finish {
  def apply(pos: Position): Finish = {
    new Finish {
      override val position = pos
    }
  }
}

abstract case class Goto private (target: String, args: Vector[Expression]) extends Expression with HasSymbol {
  def copy(target: String = this.target, args: Vector[Expression] = this.args): Goto = {
    val oldPos = this.position
    val oldID = this._id
    val oldTpe = this._tpe
    val oldSym = this._symbol

    new Goto(target, args) {
      override val position = oldPos
      this._id = oldID
      this._tpe = oldTpe
      this._symbol = oldSym
    }
  }
}

object Goto {
  def apply(target: String, args: Vector[Expression], pos: Position): Goto = {
    new Goto(target, args) {
      override val position = pos
    }
  }
}

abstract case class Generate private (target: String, args: Vector[Expression], state: Option[StateInfo]) extends Expression with HasSymbol {
  def copy(target: String = this.target, args: Vector[Expression] = this.args, state: Option[StateInfo] = this.state): Generate = {
    val oldPos = this.position
    val oldID = this._id
    val oldTpe = this._tpe
    val oldSym = this._symbol

    new Generate(target, args, state) {
      override val position = oldPos
      this._id = oldID
      this._tpe = oldTpe
      this._symbol = oldSym
    }
  }
}

object Generate {
  def apply(target: String, args: Vector[Expression], state: Option[StateInfo], pos: Position): Generate = {
    new Generate(target, args, state) {
      override val position = pos
    }
  }
}

abstract case class Commence private(proc: String, block: CommenceBlock) extends Expression with HasSymbol {
  def copy(proc: String = this.proc, block: CommenceBlock = this.block): Commence = {
    val oldPos = this.position
    val oldID = this._id
    val oldTpe = this._tpe
    val oldSym = this._symbol

    new Commence(proc, block) {
      override val position = oldPos
      _id = oldID
      _tpe = oldTpe
      _symbol = oldSym
    }
  }
}

object Commence {
  def apply(proc: String, block: CommenceBlock, pos: Position): Commence = {
    new Commence(proc, block) {
      override val position = pos
    }
  }
}

abstract case class CommenceBlock private (target: String, args: Vector[Expression]) extends AST with HasSymbol {
  def copy(target: String = this.target, args: Vector[Expression] = this.args): CommenceBlock = {
    val oldPos = this.position
    val oldID = this._id
    val oldSym = this._symbol

    new CommenceBlock(target, args) {
      override val position = oldPos
      _id = oldID
      _symbol = oldSym
    }
  }
}

object CommenceBlock {
  def apply(target: String, args: Vector[Expression], pos: Position): CommenceBlock = {
    new CommenceBlock(target, args) {
      override val position = pos
    }
  }
}

abstract case class Relay private (target: String, params: Vector[Expression], state: Option[StateInfo]) extends Expression with HasSymbol {
  def copy(target: String = this.target, params: Vector[Expression] = this.params, state: Option[StateInfo] = this.state): Relay = {
    val oldPos = this.position
    val oldID = this._id
    val oldSym = this._symbol
    val oldTpe = this._tpe

    new Relay(target, params, state) {
      override val position = oldPos
      this._id = oldID
      this._symbol = oldSym
      this._tpe = oldTpe
    }
  }
}

object Relay {
  def apply(target: String, params: Vector[Expression], state: Option[StateInfo], pos: Position): Relay = {
    new Relay(target, params, state) {
      override val position = pos
    }
  }
}

abstract case class StateInfo private (target: String, args: Vector[Expression]) extends AST with HasSymbol {
  def copy(target: String = this.target, args: Vector[Expression] = this.args): StateInfo = {
    val oldPos = this.position
    val oldID = this._id
    val oldSym = this._symbol

    new StateInfo(target, args) {
      override val position = oldPos
      this._id = oldID
      this._symbol = oldSym
    }
  }
}

object StateInfo {
  def apply(target: String, args: Vector[Expression], pos: Position): StateInfo = {
    new StateInfo(target, args) {
      override val position = pos
    }
  }
}

abstract case class Return private (expr: Expression) extends Expression {
  def copy(expr: Expression = this.expr): Return = {
    val oldPos = this.position
    val oldID = this._id
    val oldTpe = this._tpe

    new Return(expr) {
      override val position = oldPos
      this._id = oldID
      this._tpe = oldTpe
    }
  }
}

object Return {
  def apply(expr: Expression, pos: Position): Return = {
    new Return(expr) {
      override val position = pos
    }
  }
}

abstract case class Match private (expr: Expression, cases: Vector[Case]) extends Expression {
  def copy(expr: Expression = this.expr, abstracts: Vector[Case] = this.cases): Match = {
    val oldPos = this.position
    val oldID = this._id
    val oldTpe = this._tpe

    new Match(expr, abstracts) {
      override val position = oldPos
      this._id = oldID
      this._tpe = oldTpe
    }
  }
}

object Match {
  def apply(expr: Expression, cases: Vector[Case], pos: Position): Match = {
    new Match(expr, cases) {
      override val position = pos
    }
  }
}

abstract case class Case private (pattern: MatchPattern, exprs: Vector[BlockElem]) extends AST with HasType {
  def copy(pattern: MatchPattern = this.pattern, exprs: Vector[BlockElem] = this.exprs): Case = {
    val oldPos = this.position
    val oldID = this._id
    val oldTpe = this._tpe

    new Case(pattern, exprs) {
      override val position = oldPos
      this._id = oldID
      this._tpe = oldTpe
    }
  }
}

object Case {
  def apply(pattern: MatchPattern, exprs: Vector[BlockElem], pos: Position): Case = {
    new Case(pattern, exprs) {
      override val position = pos
    }
  }
}

sealed trait MatchPattern extends AST
abstract case class EnumPattern private (variant: TypeTree, patterns: Vector[MatchPattern]) extends MatchPattern {
  def copy(variant: TypeTree = this.variant, patterns: Vector[MatchPattern] = this.patterns): EnumPattern = {
    val oldPos = this.position
    val oldID = this._id

    new EnumPattern(variant, patterns) {
      override val position = oldPos
      this._id = oldID
    }
  }
}

object EnumPattern {
  def apply(variant: TypeTree, patterns: Vector[MatchPattern], pos: Position): EnumPattern = {
    new EnumPattern(variant, patterns) {
      override val position = pos
    }
  }
}

abstract case class LiteralPattern private (lit: Literal) extends MatchPattern {
  def copy(lit: Literal = this.lit): LiteralPattern = {
    val oldPos = this.position
    val oldID = this._id

    new LiteralPattern(lit) {
      override val position = oldPos
      this._id = oldID
    }
  }
}

object LiteralPattern {
  def apply(lit: Literal, pos: Position): LiteralPattern = {
    new LiteralPattern(lit) {
      override val position = pos
    }
  }
}

abstract case class IdentPattern(ident: Ident) extends MatchPattern {
  def copy(ident: Ident = this.ident): IdentPattern = {
    val oldPos = this.position
    val oldID = this._id

    new IdentPattern(ident) {
      override val position = oldPos
      this._id = oldID
    }
  }
}

object IdentPattern {
  def apply(ident: Ident, pos: Position): IdentPattern = {
    new IdentPattern(ident) {
      override val position = pos
    }
  }
}

abstract case class WildCardPattern private () extends MatchPattern with HasType {
  def copy(): WildCardPattern = {
    val oldPos = this.position
    val oldID = this._id
    val oldTpe = this._tpe

    new WildCardPattern {
      override val position = oldPos
      this._id = oldID
      this._tpe = oldTpe
    }
  }
}

object WildCardPattern {
  def apply(pos: Position): WildCardPattern = {
    new WildCardPattern {
      override val position = pos
    }
  }
}

sealed abstract class UnaryOp extends Expression with HasSymbol {
  type Expr <: Expression

  val op: Operation
  val operand: Expr
}

abstract case class StdUnaryOp private (op: Operation, operand: Expression) extends UnaryOp {
  type Expr = Expression

  def copy(op: Operation = this.op, operand: Expression = this.operand): StdUnaryOp = {
    val oldPos = this.position
    val oldID = this._id
    val oldSym = this._symbol
    val oldTpe = this._tpe

    new StdUnaryOp(op, operand) {
      override val position = oldPos
      this._id = oldID
      this._symbol = oldSym
      this._tpe = oldTpe
    }
  }
}

object StdUnaryOp {
  def apply(op: Operation, operand: Expression, pos: Position): StdUnaryOp = {
    new StdUnaryOp(op, operand) {
      override val position = pos
    }
  }
}

abstract case class HPUnaryOp private (operand: Ident) extends UnaryOp with HPExpr {
  type Expr = Ident
  val op = Operation.Neg

  def copy(operand: Ident = this.operand): HPUnaryOp = {
    val oldPos = this.position
    val oldID = this._id
    val oldTpe = this._tpe
    val oldSym = this._symbol
    val oldExpr = this._sortedExpr

    new HPUnaryOp(operand) {
      override val position = oldPos

      this._id = oldID
      this._tpe = oldTpe
      this._symbol = oldSym
      this._sortedExpr = oldExpr
    }
  }
}

object HPUnaryOp {
  def apply(operand: Ident, pos: Position): HPUnaryOp = {
    new HPUnaryOp(operand) {
      override val position = pos
    }
  }
}

sealed abstract class BinOp extends Expression with HasSymbol {
  type Expr <: Expression

  val op: Operation
  val left: Expr
  val right: Expr
}

abstract case class StdBinOp private (op: Operation, left: Expression, right: Expression) extends BinOp {
  type Expr = Expression

  def copy(op: Operation = this.op, left: Expression = this.left, right: Expression = this.right): StdBinOp = {
    val oldPos = this.position
    val oldID = this._id
    val oldSym = this._symbol
    val oldTpe = this._tpe

    new StdBinOp(op, left, right) {
      override val position = oldPos
      this._id = oldID
      this._symbol = oldSym
      this._tpe = oldTpe
    }
  }
}

object StdBinOp {
  def apply(op: Operation, left: Expression, right: Expression, pos: Position): StdBinOp = {
    new StdBinOp(op, left, right) {
      override val position = pos
    }
  }
}

abstract case class HPBinOp private (left: Expression with HPExpr, right: Expression with HPExpr) extends BinOp with HPExpr {
  type Expr = Expression with HPExpr
  val op: Operation = Operation.Add

  def copy(
    left: Expression with HPExpr = this.left,
    right: Expression with HPExpr = this.right
  ): HPBinOp = {
    val oldPos = this.position
    val oldID = this._id
    val oldSym = this._symbol
    val oldTpe = this._tpe
    val oldExpr = this._sortedExpr

    new HPBinOp(left, right) {
      override val position = oldPos
      this._id = oldID
      this._symbol = oldSym
      this._tpe = oldTpe
      this._sortedExpr = oldExpr
    }
  }
}

object HPBinOp {
  def apply(left: Expression with HPExpr, right: Expression with HPExpr, pos: Position): HPBinOp = {
    new HPBinOp(left, right) {
      override val position = pos
    }
  }
}

abstract case class DeReference private (expr: Expression) extends Expression {
  def copy(expr: Expression = this.expr): DeReference = {
    val oldPos = this.position
    val oldID = this._id
    val oldTpe = this._tpe

    new DeReference(expr) {
      override val position = oldPos
      _id = oldID
      _tpe = oldTpe
    }
  }
}

object DeReference {
  def apply(expr: Expression, pos: Position): DeReference = {
    new DeReference(expr) {
      override val position = pos
    }
  }
}

abstract case class TypeTree private (expr: TypeAST, hp: Vector[HPExpr], tp: Vector[TypeTree], isPointer: Boolean) extends AST with HasType with HasSymbol {
  def copy(expr: TypeAST = this.expr, hp: Vector[HPExpr] = this.hp, tp: Vector[TypeTree] = this.tp, isPointer: Boolean = this.isPointer): TypeTree = {
    val oldPos = this.position
    val oldID = this._id
    val oldSym = this._symbol
    val oldTpe = this._tpe

    new TypeTree(expr, hp, tp, isPointer) {
      override val position = oldPos
      this._id = oldID
      this._symbol = oldSym
      this._tpe = oldTpe
    }
  }
}

object TypeTree {
  def apply(expr: TypeAST, hp: Vector[HPExpr], tp: Vector[TypeTree], isPointer: Boolean, pos: Position): TypeTree = {
    new TypeTree(expr, hp, tp, isPointer) {
      override val position = pos
    }
  }
}

abstract case class ThisType private () extends TypeAST with HasType {
  def copy(): ThisType = {
    val oldPos = this.position
    val oldID = this._id
    val oldSym = this._symbol
    val oldTpe = this._tpe

    new ThisType {
      override val position = oldPos
      this._id = oldID
      this._symbol = oldSym
      this._tpe = oldTpe
    }
  }
}

object ThisType {
  def apply(pos: Position): ThisType = {
    new ThisType {
      override val position = pos
    }
  }
}

abstract case class CastType private (from: TypeTree, to: TypeTree) extends TypeAST with HasType {
  def copy(from: TypeTree = this.from, to: TypeTree = this.to): CastType = {
    val oldPos = this.position
    val oldID = this._id
    val oldSym = this._symbol
    val oldTpe = this._tpe

    new CastType(from, to) {
      override val position = oldPos
      this._id = oldID
      this._tpe = oldTpe
      this._symbol = oldSym
    }
  }
}

object CastType {
  def apply(from: TypeTree, to: TypeTree, pos: Position): CastType = {
    new CastType(from, to) {
      override val position = pos
    }
  }
}

sealed trait Annotation
object Annotation {
  case class BuiltIn(name: String, args: Vector[String], ret: String) extends Annotation
}

case class Point(line: Int, column: Int) extends Ordered[Point] {
  override def compare(that: Point): Int = {
    if(this == that) 0
    else if (this.line < that.line) -1
    else if (this.line == that.line && this.column < that.column) -1
    else 1
  }
}

object Point {
  def empty: Point = Point(0, 0)
}


case class Position(filename: String, start: Point, end: Point)
object Position {
  def apply(ctx: org.antlr.v4.runtime.ParserRuleContext)(implicit file: Filename): Position = {
    val startLine = ctx.getStart.getLine
    val startColumn = ctx.getStart.getCharPositionInLine + 1
    val start = Point(startLine, startColumn)
    val endLine = ctx.getStop.getLine
    val endColumn = ctx.getStop.getCharPositionInLine + ctx.getStop.getText.length + 1
    val end = Point(endLine, endColumn)

    Position(file.name, start, end)
  }

  def apply(start: AST, end: AST): Position = {
    val filename = start.position.filename
    val startPos = start.position.start
    val endPos = end.position.end

    Position(filename, startPos, endPos)
  }

  def apply(tree: AST): Position = {
    val pos = tree.position
    Position(pos.filename, pos.start, pos.end)
  }

  def empty: Position = Position("", Point.empty, Point.empty)
}