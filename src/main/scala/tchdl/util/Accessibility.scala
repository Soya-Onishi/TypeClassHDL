package tchdl.util

sealed trait Accessibility

object Accessibility {
  case object Public extends Accessibility
  case object Private extends Accessibility
  case class Restrict(allow: NameSpace) extends Accessibility
}
