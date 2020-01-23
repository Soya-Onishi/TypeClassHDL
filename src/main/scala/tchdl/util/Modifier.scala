package tchdl.util

trait Modifier {
  val value: BigInt

  def |(that: Modifier): Modifier = new Modifier { val value: BigInt = this.value | that.value }
  def &(that: Modifier): Modifier = new Modifier { val value: BigInt = this.value & that.value }
  def hasFlag(flag: Modifier): Boolean = (this.value & flag.value) > 0
  def hasNoFlag(flag: Modifier): Boolean = !this.hasFlag(flag)
}

object Modifier {
  def apply(name: String): Modifier = name match {
    case "input" => Input
    case "internal" => Internal
    case "output" => Output
    case "reg" => Register
    case "public" => Public
    case "module" => Module
    case "sibling" => Sibling
    case "parent" => Parent
  }

  def apply(names: Iterable[String]): Modifier =
    names.foldLeft[Modifier](NoModifier){
      case (acc, name) => acc | apply(name)
    }


  private val seed = BigInt(1)

  case object NoModifier extends Modifier { val value = 0x0 }
  case object Input extends Modifier      { val value = seed << 0 }
  case object Internal extends Modifier   { val value = seed << 1 }
  case object Output extends Modifier     { val value = seed << 2 }
  case object Register extends Modifier   { val value = seed << 3 }
  case object Public extends Modifier     { val value = seed << 4 }
  case object Module extends Modifier     { val value = seed << 5 }
  case object Sibling extends Modifier    { val value = seed << 6 }
  case object Parent extends Modifier     { val value = seed << 7 }
}
