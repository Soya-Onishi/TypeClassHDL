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
  def setFlag(flag: Modifier): this.type = { _flag = flag; this }
  def addFlag(flag: Modifier): this.type = { _flag |= flag; this }
  def hasFlag(flag: Modifier): Boolean = { _flag.hasFlag(flag) }
  def flag: Modifier = _flag
}

object Symbol {
  class TypeSymbol(val name: String, val namespace: Vector[String], owner: Option[Symbol], tpe: Type) extends Symbol(owner, tpe)
  object TypeSymbol {
    def apply(name: String, namespace: Vector[String], tpe: Type, owner: Option[Symbol] = None): TypeSymbol =
      new TypeSymbol(name, namespace, owner, tpe)
  }

  /*
  class ClassSymbol(name: String, namespace: Vector[String], owner: Option[Symbol], tpe: Type) extends TypeSymbol(name, namespace, owner, tpe)
  object ClassSymbol {
    def apply(name: String, namespace: Vector[String], tpe: Type, owner: Option[Symbol] = None): ClassSymbol =
      new ClassSymbol(name, namespace, owner, tpe)
  }

  class StructSymbol(name: String, namespace: Vector[String], owner: Option[Symbol], tpe: Type) extends TypeSymbol(name, namespace, owner, tpe)
  object StructSymbol {
    def apply(name: String, namespace: Vector[String], tpe: Type, owner: Option[Symbol] = None): StructSymbol =
      new StructSymbol(name, namespace, owner, tpe)
  }
  */

  class TermSymbol(
    val name: String,
    val namespace: Vector[String],
    owner: Option[Symbol],
    tpe: Type
  ) extends Symbol(owner, tpe)
  object TermSymbol {
    def apply(name: String, namespace: Vector[String], tpe: Type, owner: Option[Symbol]): TermSymbol =
      new TermSymbol(name, namespace, owner, tpe)
  }
}

