package tchdl.util

class Modifier(_value: Option[BigInt] = None) {
  val value: BigInt = _value.getOrElse(BigInt(1) << Modifier.count)

  def |(that: Modifier): Modifier = new Modifier(Some(this.value | that.value))
  def &(that: Modifier): Modifier = new Modifier(Some(this.value & that.value))
  def hasFlag(flag: Modifier): Boolean = (this.value & flag.value) > 0
  def hasNoFlag(flag: Modifier): Boolean = !this.hasFlag(flag)
  override def equals(obj: Any): Boolean = obj match {
    case that: Modifier => this.value == that.value
    case _ => false
  }

  override def toString: String = {
    Modifier.modifiers
      .filter{ case (key, _) => this.hasFlag(key) }
      .map{ case (_, name) => name }
      .mkString(" | ")
  }
}

object Modifier {
  def apply(name: String): Modifier = name match {
    case "input" => Input
    case "internal" => Internal
    case "output" => Output
    case "reg" => Register
    case "public" => Public
    case "sibling" => Sibling
    case "parent" => Parent
  }

  def apply(names: Iterable[String]): Modifier =
    names.foldLeft[Modifier](NoModifier){
      case (acc, name) => acc | apply(name)
    }

  private var _count = 1
  def count: Int = {
    val c = _count
    _count = _count + 1
    c
  }

  lazy val modifiers = Map (
    Input -> "Input",
    Internal -> "Internal",
    Output -> "Output",
    Register -> "Register",
    Public -> "Public",
    Sibling -> "Sibling",
    Parent -> "Parent",
    Child -> "Child",

    Interface -> "Interface",
    Trait -> "Trait",

    Local -> "Local",
    Field -> "Field",
  )

  case object NoModifier extends Modifier(Some(0))
  case object Input extends Modifier
  case object Internal extends Modifier
  case object Output extends Modifier
  case object Register extends Modifier
  case object Public extends Modifier
  case object Sibling extends Modifier
  case object Parent extends Modifier
  case object Child extends Modifier

  case object Interface extends Modifier
  case object Trait extends Modifier

  case object Local extends Modifier
  case object Field extends Modifier
}
