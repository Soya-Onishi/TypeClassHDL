package tchdl.util

import tchdl.ast.Definition

abstract class Symbol(protected var owner: Option[Symbol], __tpe: Type) {
  val name: String
  val namespace: Vector[String]

  def getOwner: Option[Symbol] = owner
  def setOnwer(owner: Symbol): Unit = this.owner = Some(owner)

  private var isAlreadyReferenced = false
  private var _tpe: Type = __tpe
  def setTpe(tpe: Type): Unit = _tpe = tpe
  def tpe: Either[Error, Type] = {
    _tpe match {
      case _: Type.TypeGenerator if isAlreadyReferenced =>
        ???
      case gen: Type.TypeGenerator =>
        isAlreadyReferenced = true
        val tpe = gen.generate()
        _tpe = tpe
        Right(tpe)
      case tpe =>
        Right(tpe)
    }
  }

  private var _flag: Modifier = Modifier.NoModifier
  def setFlag(flag: Modifier): Unit = { _flag = flag }
  def addFlag(flag: Modifier): Unit = { _flag |= flag }
  def flag: Modifier = _flag
}

object Symbol {
  class TypeSymbol(val name: String, val namespace: Vector[String], __tpe: Type) extends Symbol(None, __tpe)

  object TypeSymbol {
    def apply(name: String, namespace: Vector[String], tpe: Type): TypeSymbol =
      new TypeSymbol(name, namespace, tpe)
  }

  class TermSymbol(
    val name: String,
    val namespace: Vector[String],
    _owner: Option[Symbol],
    _tpe: Type
  ) extends Symbol(_owner, _tpe)

  object TermSymbol {
    def apply(name: String, namespace: Vector[String], owner: Option[Symbol], ctx: Context, tree: Definition): TermSymbol =
      new TermSymbol(name, namespace, owner, Type.TypeGenerator(ctx, tree))
  }
}

