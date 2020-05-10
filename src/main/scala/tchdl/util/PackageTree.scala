package tchdl.util

import tchdl.util.TchdlException.ImplementationErrorException
import scala.collection.mutable

object PackageRoot extends PackageNode("__root__")

class PackageNode(val name: String) {
  private val nodes = mutable.Map[String, PackageNode]()
  private val contexts = mutable.Map[String, Context.RootContext]()

  def getContext(filename: String): Context.RootContext =
    contexts.get(filename) match {
      case Some(ctx) => ctx
      case None =>
        val msg = s"There is no Context related to filename[$filename]"
        throw new ImplementationErrorException(msg)
    }

  def appendContext(filename: String, ctx: Context.RootContext): Unit =
    contexts(filename) = ctx

  def getNode(name: String): Option[PackageNode] = nodes.get(name)
  def appendNode(node: PackageNode): Unit = nodes(node.name) = node
}

object PackageNode {
  def apply(name: String): PackageNode = new PackageNode(name)
}
