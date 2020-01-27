package tchdl.util

class Symbol(
  val name: String,
  val namespace: Vector[String],
  private var _owner: Option[Symbol] = None
) {
  def owner: Option[Symbol] = _owner
  def setOwner(owner: Symbol): Unit = _owner = Some(owner)

  private var _tpe: Option[Type] = None
  def tpe: Type = _tpe.get
  def setTpe(tpe: Type): Unit = _tpe = Some(tpe)

  private var _flag: Modifier = Modifier.NoModifier
  def setFlag(flag: Modifier): Unit = { _flag = flag }
  def addFlag(flag: Modifier): Unit = { _flag |= flag }
  def flag: Modifier = _flag
}

object Symbol {
  def apply(name: String, namespace: Vector[String]): Symbol = new Symbol(name, namespace, None)
  def apply(name: String, namespace: Vector[String], owner: Symbol): Symbol = new Symbol(name, namespace, Some(owner))
}
