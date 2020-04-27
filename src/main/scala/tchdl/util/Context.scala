package tchdl.util

class Context(
 val parent: Option[Context],
 val owner: Option[Symbol],
 val name: Option[String],
) {
  val scope: Scope = new Scope
  val path: NameSpace = NameSpace(this)
  private var errors: Vector[Error] = Vector.empty

  def enclosedClass: Option[Symbol.TypeSymbol] = {
    owner match {
      case None => None
      case Some(symbol: Symbol.StructSymbol) => Some(symbol)
      case Some(symbol: Symbol.ModuleSymbol) => Some(symbol)
      case Some(_) => parent.flatMap(_.enclosedClass)
    }
  }

  def append(symbol: Symbol): Either[Error, Unit] = scope.append(symbol)
  def lookup(name: String): Either[Error, Symbol] = scope.lookup(name) match {
    case Some(elem) => Right(elem)
    case None => parent match {
      case Some(owner) => owner.lookup(name)
      case None => Left(Error.SymbolNotFound(name))
    }
  }

  def appendError(err: Error): Unit = parent match {
    case Some(owner) => owner.appendError(err)
    case None => errors = err +: errors
  }

  def reAppend(syms: Symbol*): Either[Error, Unit] = {
    syms.map(append).find(_.isLeft) match {
      case Some(left) => left
      case None => Right(())
    }
  }

  private var blkID: Int = 0
  def getBlkID: Int = {
    val id = blkID
    blkID += 1
    id
  }
}

object Context {
  def apply(owner: Context): Context = new Context(Some(owner), owner.owner, None)
  def apply(owner: Context, name: String) = new Context(Some(owner), owner.owner, Some(name))
  def apply(owner: Context, name: String, symbol: Symbol): Context = new Context(Some(owner), Some(symbol), Some(name))
  def root(pkgName: NameSpace): Context = new Context(None, None, Some(pkgName.toVec.mkString(".")))
}

class NameSpace(val namespace: Vector[String]) {
  def append(name: String) = new NameSpace(namespace.appended(name))
  def toVec: Vector[String] = namespace

  override def hashCode(): Int = namespace.hashCode
}

object NameSpace {
  def apply(ctx: Context): NameSpace = {
    (ctx.parent, ctx.name) match {
      case (Some(parent), None) => parent.path
      case (Some(parent), Some(name)) => parent.path.append(name)
      case (None, name) =>
        // name must be Some because when ctx.owner is None,
        // it is top level context and it should have package name.
        new NameSpace(Vector(name.get))
    }
  }

  def apply(pkgName: Vector[String]): NameSpace = new NameSpace(pkgName)
  def apply(pkgName: String*): NameSpace = new NameSpace(pkgName.toVector)
  def empty = new NameSpace(Vector.empty)
}
