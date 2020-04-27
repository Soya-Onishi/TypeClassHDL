package tchdl.util

sealed trait Visibility

object Visibility {
  case object Public extends Visibility
  case object Private extends Visibility
  case class Restrict(allow: NameSpace) extends Visibility
}
