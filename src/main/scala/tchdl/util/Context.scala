package tchdl.util

abstract class Context {
  val scope: Scope = new Scope
  def path: NameSpace

  def append(symbol: Symbol): Either[Error, Unit] = scope.append(symbol)
  def lookup(name: String): Either[Error, Symbol]

  def reAppend(syms: Symbol*): Either[Error, Unit] = {
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
}

object Context {
  def apply(owner: Context, symbol: Symbol, self: Type.RefType): NodeContext =
    new NodeContext(owner, symbol, Some(self), None)

  def apply(owner: Context, symbol: Symbol): NodeContext =
    new NodeContext(owner, symbol, None, Some(symbol.name))

  def apply(owner: NodeContext, self: Type.RefType): NodeContext =
    new NodeContext(owner, owner.owner, Some(self), None)

  def apply(owner: NodeContext): NodeContext =
    new NodeContext(owner, owner.owner, owner.self, None)

  def blk(owner: NodeContext): NodeContext =
    new NodeContext(owner, owner.owner, owner.self, Some(owner.getBlkID.toString))

  def root(pkgName: Vector[String]): RootContext = new RootContext(pkgName)

  class RootContext(pkgName: Vector[String]) extends Context {
    import scala.collection.mutable

    override val path: NameSpace = NameSpace(pkgName, Vector.empty, None)

    override def lookup(name: String): Either[Error, Symbol] = scope.lookup(name) match {
      case Some(elem) => Right(elem)
      case None => Left(Error.SymbolNotFound(name))
    }

    private[this] val importedInterfaces = mutable.Map[String, Symbol.InterfaceSymbol]()
    def appendInterface(symbol: Symbol.InterfaceSymbol): Unit = {
      importedInterfaces(symbol.name) = symbol
    }
    override def interfaceTable: Map[String, Symbol.InterfaceSymbol] = importedInterfaces.toMap
  }

  class NodeContext(
    val parent: Context,
    val owner: Symbol,
    val self: Option[Type.RefType],
    name: Option[String]
  ) extends Context {
    override def path: NameSpace = {
      name match {
        case Some(n) => path.appendName(n)
        case None => path
      }
    }

    def lookup(name: String): Either[Error, Symbol] = scope.lookup(name) match {
      case Some(elem) => Right(elem)
      case None => parent.lookup(name)
    }

    override def interfaceTable: Map[String, Symbol.InterfaceSymbol] = parent.interfaceTable
  }


}

case class NameSpace(pkgName: Vector[String], path: Vector[String], name: Option[String]) {
  def appendName(name: String): NameSpace = {
    this.name match {
      case None => this.copy(name = Some(name))
      case Some(n) =>
        val path = this.path ++ Vector(n)
        this.copy(path = path, name = Some(name))
    }
  }
}

object NameSpace {
  def empty: NameSpace = NameSpace(Vector.empty, Vector.empty, None)
}

object ImplementId {
  private var _id = 0
  def id(): Int = {
    val num = _id
    _id += 1
    num
  }
}

