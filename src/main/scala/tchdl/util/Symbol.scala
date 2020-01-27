package tchdl.util

abstract class Symbol(protected var owner: Option[Symbol]) {
  val name: String
  val namespace: Vector[String]

  def getOwner: Option[Symbol] = owner
  def setOnwer(owner: Symbol): Unit = this.owner = Some(owner)

  private var _tpe: Option[Type] = None
  def tpe: Type = _tpe.get
  def setTpe(tpe: Type): Unit = _tpe = Some(tpe)

  private var _flag: Modifier = Modifier.NoModifier
  def setFlag(flag: Modifier): Unit = { _flag = flag }
  def addFlag(flag: Modifier): Unit = { _flag |= flag }
  def flag: Modifier = _flag
}

case class TypeSymbol(name: String, namespace: Vector[String]) extends Symbol(None)
case class TermSymbol(name: String, namespace: Vector[String], _owner: Option[Symbol]) extends Symbol(_owner)
