package tchdl.util

import tchdl.util.TchdlException.ImplementationErrorException

import scala.reflect.ClassTag
import scala.reflect.runtime.universe.TypeTag


abstract class Context {
  val scope: Scope = new Scope
  val isStatic: Boolean
  def path: NameSpace
  def root: Context.RootContext

  def self: Option[Type.RefType]

  def append(symbol: Symbol)(implicit global: GlobalData): Either[Error, Unit]
  def lookup[T <: Symbol](name: String)(implicit global: GlobalData, ev0: ClassTag[T], ev1: TypeTag[T]): LookupResult[T]

  def reAppend(syms: Symbol*)(implicit global: GlobalData): Either[Error, Unit] = {
    syms.map(append).find(_.isLeft) match {
      case Some(left) => left
      case None => Right(())
    }
  }

  def interfaceTable: Map[String, Symbol.InterfaceSymbol]

  private var blkID: Int = 0
  def getBlkID: Int = {
    val id = blkID
    blkID += 1
    id
  }

  def hpBounds: Vector[HPBound]
  def tpBounds: Vector[TPBound]
}

object Context {
  def apply(owner: Context, symbol: Symbol, isStatic: Boolean = false): NodeContext =
    new NodeContext(owner, symbol, owner.self, symbol.path, isStatic)

  def apply(owner: NodeContext, self: Type.RefType): NodeContext =
    new NodeContext(owner, owner.owner, Some(self), owner.path, owner.isStatic)

  def apply(owner: NodeContext): NodeContext =
    new NodeContext(owner, owner.owner, owner.self, owner.path, owner.isStatic)

  def blk(owner: NodeContext): NodeContext =
    new NodeContext(owner, owner.owner, owner.self, owner.path.appendInnerName(owner.getBlkID.toString), owner.isStatic)

  def root(pkgName: Vector[String]): RootContext = new RootContext(pkgName)

  class RootContext(pkgName: Vector[String]) extends Context {
    override val path: NameSpace = NameSpace(pkgName, Vector.empty, Vector.empty)
    override val self: Option[Type.RefType] = None
    override val isStatic: Boolean = false
    override def root: Context.RootContext = this

    override def lookup[T <: Symbol](name: String)(implicit global: GlobalData, ev0: ClassTag[T], ev1: TypeTag[T]): LookupResult[T] = scope.lookup(name) match {
      case Some(elem: T) => LookupResult.LookupSuccess(elem)
      case Some(elem) => LookupResult.LookupFailure(Error.RequireSymbol[T](elem))
      case None => importedSymbols.lookup(name) match {
        case Some(elem: T) => LookupResult.LookupSuccess(elem)
        case Some(elem) => LookupResult.LookupFailure(Error.RequireSymbol[T](elem))
        case None => preludeSymbols.lookup(name) match {
          case Some(elem: T) => LookupResult.LookupSuccess(elem)
          case Some(elem) => LookupResult.LookupFailure(Error.RequireSymbol[T](elem))
          case None =>
            global.rootPackage.search(pkgName)
              .getOrElse(throw new ImplementationErrorException(s"package symbol[${pkgName.mkString("::")}] must be found"))
              .lookup(name)
        }
      }
    }

    override def append(symbol: Symbol)(implicit global: GlobalData): Either[Error, Unit] = {
      val intoScope = this.scope.append(symbol)
      val intoPackage = global.rootPackage.search(pkgName)
        .getOrElse(throw new ImplementationErrorException(s"package symbol[${pkgName.mkString("::")}] must be found"))
        .append(symbol)

      (intoScope, intoPackage) match {
        case (Left(err0), Left(err1)) => Left(Error.MultipleErrors(err0, err1))
        case (Left(err), _) => Left(err)
        case (_, Left(err)) => Left(err)
        case (Right(_), Right(_)) => Right(())
      }
    }

    private val preludeSymbols = Scope.empty
    def appendPrelude(symbol: Symbol): Either[Error, Unit] =
      preludeSymbols.append(symbol)

    private val importedSymbols = Scope.empty
    def appendImportSymbol(symbol: Symbol): Either[Error, Unit] =
      importedSymbols.append(symbol)

    override def interfaceTable: Map[String, Symbol.InterfaceSymbol] =
      this.scope.toMap.collect{
        case (name, interface: Symbol.InterfaceSymbol) => name -> interface
      }

    override def hpBounds: Vector[HPBound] = Vector.empty
    override def tpBounds: Vector[TPBound] = Vector.empty
  }

  class NodeContext(
    val parent: Context,
    val owner: Symbol,
    val self: Option[Type.RefType],
    val path: NameSpace,
    val isStatic: Boolean
  ) extends Context {
    override def root: Context.RootContext = parent.root

    def append(symbol: Symbol)(implicit global: GlobalData): Either[Error, Unit] = scope.append(symbol)
    def lookup[T <: Symbol](name: String)(implicit global: GlobalData, ev0: ClassTag[T], ev1: TypeTag[T]): LookupResult[T] =
      lookingUp[T](name){ parent.lookup(name) }

    def lookupDirectLocal[T <: Symbol : ClassTag : TypeTag](name: String): LookupResult[T] = {
      lookingUp[T](name) {
        parent match {
          case p: Context.NodeContext if p.owner == this.owner => p.lookupDirectLocal[T](name)
          case _ => LookupResult.LookupFailure(Error.SymbolNotFound(name))
        }
      }
    }

    def lookupLocal[T <: Symbol : ClassTag : TypeTag](name: String): LookupResult[T] =
      lookingUp[T](name){
        parent match {
          case p: Context.NodeContext if p.owner.isTermSymbol => p.lookupLocal[T](name)
          case _ => LookupResult.LookupFailure(Error.SymbolNotFound(name))
        }
      }

    private def lookingUp[T <: Symbol : ClassTag : TypeTag](name: String)(forNone: => LookupResult[T]): LookupResult[T] =
      scope.lookup(name) match {
        case Some(elem: T) => LookupResult.LookupSuccess(elem)
        case Some(elem) => LookupResult.LookupFailure(Error.RequireSymbol[T](elem))
        case None => forNone
      }


    def hpBounds: Vector[HPBound] = {
      def hpBound(symbol: Symbol): Vector[HPBound] = symbol match {
        case owner: Symbol with HasParams => owner.hpBound
        case _ => Vector.empty
      }

      parent match {
        case _: Context.RootContext => hpBound(owner)
        case ctx: Context.NodeContext if ctx.owner == this.owner => parent.hpBounds
        case _: Context.NodeContext => hpBound(owner) ++ parent.hpBounds
      }
    }

    def tpBounds: Vector[TPBound] = {
      def tpBound(symbol: Symbol): Vector[TPBound] = symbol match {
        case owner: Symbol with HasParams => owner.tpBound
        case _ => Vector.empty
      }

      parent match {
        case _: Context.RootContext => tpBound(owner)
        case ctx: Context.NodeContext if ctx.owner == this.owner => parent.tpBounds
        case _: Context.NodeContext => tpBound(owner) ++ parent.tpBounds
      }
    }

    def owners: Vector[Symbol] = {
      def loop(ctx: Context, owner: Symbol): Vector[Symbol] = {
        ctx match {
          case _: Context.RootContext => Vector.empty
          case ctx: Context.NodeContext if ctx.owner == owner => loop(ctx.parent, owner)
          case ctx: Context.NodeContext => ctx.owner +: loop(ctx.parent, ctx.owner)
        }
      }

      this.owner +: loop(this, this.owner)
    }

    override def interfaceTable: Map[String, Symbol.InterfaceSymbol] = parent.interfaceTable
  }
}

case class NameSpace(pkgName: Vector[String], rootPath: Vector[String], innerPath: Vector[String]) {
  override def hashCode(): Int = pkgName.hashCode + rootPath.hashCode + innerPath.hashCode
  def name: Option[String] = innerPath.lastOption orElse rootPath.lastOption

  def appendComponentName(name: String): NameSpace = {
    assert(innerPath.isEmpty)
    this.copy(rootPath = this.rootPath :+ name)
  }

  def appendInnerName(name: String): NameSpace = this.copy(innerPath = this.innerPath :+ name)
}

object NameSpace {
  def empty: NameSpace = NameSpace(Vector.empty, Vector.empty, Vector.empty)
}

object ImplementId {
  private var _id = 0
  def id(): Int = {
    val num = _id
    _id += 1
    num
  }
}

