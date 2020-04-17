package tchdl.util

class Context(
 val parent: Option[Context],
 val name: Option[String],
) {
  val scope: Scope = new Scope
  val namespace: NameSpace = NameSpace(this)
  private var errors: Vector[Error] = Vector.empty

  def append(symbol: Symbol): Either[Error, Unit] = scope.append(symbol)
  def lookup(name: String): Either[Error, Symbol] = scope.lookup(name) match {
    case Some(elem) => Right(elem)
    case None => parent match {
      case Some(owner) => owner.lookup(name)
      case None => Left(???)
    }
  }

  def appendError(err: Error): Unit = parent match {
    case Some(owner) => owner.appendError(err)
    case None => errors = err +: errors
  }
}

object Context {
  def apply(owner: Context): Context = new Context(Some(owner), None)
  def apply(owner: Context, name: String): Context = new Context(Some(owner), Some(name))
  def root(pkgName: String): Context = new Context(None, Some(pkgName))
}

class NameSpace(val namespace: Vector[String]) {
  def append(name: String) = new NameSpace(namespace.appended(name))
  def toVec: Vector[String] = namespace
}

object NameSpace {
  def apply(ctx: Context): NameSpace = {
    (ctx.parent, ctx.name) match {
      case (Some(parent), None) => parent.namespace
      case (Some(parent), Some(name)) => parent.namespace.append(name)
      case (None, name) =>
        // name must be Some because when ctx.owner is None,
        // it is top level context and it should have package name.
        new NameSpace(Vector(name.get))
    }
  }

  def empty = new NameSpace(Vector.empty)
}
