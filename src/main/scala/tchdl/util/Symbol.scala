package tchdl.util

import tchdl.util.TchdlException.ImplimentationErrorException

abstract class Symbol(__tpe: Type, __flag: Modifier) {
  val name: String
  val path: NameSpace
  val visibility: Visibility

  private var isAlreadyReferenced = false
  private var _tpe: Type = __tpe

  def setTpe(tpe: Type): Unit = _tpe = tpe

  def tpe: Type = {
    val isReferenced = isAlreadyReferenced
    isAlreadyReferenced = true

    _tpe match {
      case _: Type.TypeGenerator if isReferenced =>
        // TODO: send cyclic reference error to context
        Type.ErrorType
      case gen: Type.TypeGenerator =>
        val tpe = gen.generate
        _tpe = tpe
        tpe
      case tpe => tpe
    }
  }

  private var _flag: Modifier = __flag

  def setFlag(flag: Modifier): this.type = {
    _flag = flag;
    this
  }

  def addFlag(flag: Modifier): this.type = {
    _flag |= flag;
    this
  }

  def hasFlag(flag: Modifier): Boolean = {
    _flag.hasFlag(flag)
  }

  def flag: Modifier = _flag

  override def equals(obj: Any): Boolean = obj match {
    case sym: Symbol => this.getClass == sym.getClass && this.path == sym.path
    case _ => false
  }

  override def hashCode(): Int = this.getClass.hashCode + this.path.hashCode + this.name.hashCode

  def asTypeSymbol: Symbol.TypeSymbol = this.asInstanceOf[Symbol.TypeSymbol]

  def asTermSymbol: Symbol.TermSymbol = this.asInstanceOf[Symbol.TermSymbol]
}

trait HasOwner extends Symbol {
  val owner: Symbol
}

object Symbol {

  abstract class TypeSymbol(tpe: Type, flags: Modifier) extends Symbol(tpe, flags)

  class StructSymbol(
    val name: String,
    val path: NameSpace,
    val visibility: Visibility,
    flags: Modifier,
    tpe: Type
  ) extends TypeSymbol(tpe, flags)

  object StructSymbol {
    def apply(name: String, path: NameSpace, visibility: Visibility, flags: Modifier, tpe: Type): StructSymbol =
      new StructSymbol(name, path, visibility, flags, tpe)
  }

  class ModuleSymbol(
    val name: String,
    val path: NameSpace,
    val visibility: Visibility,
    flags: Modifier,
    tpe: Type
  ) extends TypeSymbol(tpe, flags)

  object ModuleSymbol {
    def apply(name: String, path: NameSpace, visibility: Visibility, flags: Modifier, tpe: Type): ModuleSymbol =
      new ModuleSymbol(name, path, visibility, flags, tpe)
  }

  class TypeParamSymbol(
    val name: String,
    val path: NameSpace,
    val owner: Symbol,
    tpe: Type
  ) extends TypeSymbol(tpe, Modifier.NoModifier) with HasOwner {
    override val visibility: Visibility = Visibility.Private
  }

  object TypeParamSymbol {
    def apply(name: String, path: NameSpace, owner: Symbol, tpe: Type): TypeParamSymbol =
      new TypeParamSymbol(name, path, owner, tpe)
  }

  abstract class TermSymbol(tpe: Type, flags: Modifier) extends Symbol(tpe, flags)

  class VariableSymbol(
    val name: String,
    val path: NameSpace,
    val visibility: Visibility,
    val owner: Symbol,
    flags: Modifier,
    tpe: Type
  ) extends TermSymbol(tpe, flags) with HasOwner

  object VariableSymbol {
    def apply(name: String, path: NameSpace, visibility: Visibility, owner: Symbol, flags: Modifier, tpe: Type): VariableSymbol =
      new VariableSymbol(name, path, visibility, owner, flags, tpe)
  }

  class MethodSymbol(
    val name: String,
    val path: NameSpace,
    val visibility: Visibility,
    val owner: Symbol,
    flags: Modifier,
    tpe: Type
  ) extends TermSymbol(tpe, flags) with HasOwner

  object MethodSymbol {
    def apply(name: String, path: NameSpace, visibility: Visibility, owner: Symbol, flags: Modifier, tpe: Type): MethodSymbol =
      new MethodSymbol(name, path, visibility, owner, flags, tpe)
  }

  class AlwaysSymbol(
    val name: String,
    val path: NameSpace,
    val owner: Symbol
  ) extends TermSymbol(Type.NoType, Modifier.NoModifier) with HasOwner {
    override val visibility: Visibility = Visibility.Private
  }

  object AlwaysSymbol {
    def apply(name: String, path: NameSpace, owner: Symbol): AlwaysSymbol =
      new AlwaysSymbol(name, path, owner)
  }

  class StageSymbol(
    val name: String,
    val path: NameSpace,
    val owner: Symbol,
    tpe: Type
  ) extends TermSymbol(tpe, Modifier.NoModifier) with HasOwner {
    override val visibility: Visibility = Visibility.Private
  }

  object StageSymbol {
    def apply(name: String, path: NameSpace, owner: Symbol, tpe: Type): StageSymbol =
      new StageSymbol(name, path, owner, tpe)
  }

  class StateSymbol(
    val name: String,
    val path: NameSpace,
    val owner: Symbol
  ) extends Symbol(Type.NoType, Modifier.NoModifier) with HasOwner {
    override val visibility: Visibility = Visibility.Private
  }

  object StateSymbol {
    def apply(name: String, path: NameSpace, owner: Symbol): StateSymbol =
      new StateSymbol(name, path, owner)
  }

  object ErrorSymbol extends Symbol(Type.ErrorType, Modifier.NoModifier) {
    override val name: String = "<error>"
    override val path: NameSpace = NameSpace.empty
    override val visibility: Visibility = Visibility.Public
  }

  import scala.collection.mutable

  // There is null. However, this null will never go to outside of this builtin table.
  // because appendBuiltin and lookupBuiltin see whether Map's value is null or not, and
  // if it is null, methods address that case.
  private val builtin: mutable.Map[String, Symbol.TypeSymbol] = mutable.Map[String, Symbol.TypeSymbol](
    "Int32" -> null,
    "UInt32" -> null,
    "String" -> null,
    "Unit" -> null,
    "Bit" -> null
  )

  def appendBuiltin(symbol: Symbol.TypeSymbol): Unit = {
    builtin.get(symbol.name) match {
      case None => throw new ImplimentationErrorException(s"${symbol.name} is not a builtin type")
      case Some(null) => builtin(symbol.name) = symbol
      case Some(_) => throw new ImplimentationErrorException(s"${symbol.name} is already assigned")
    }
  }

  def lookupBuiltin(name: String): Symbol.TypeSymbol = {
    builtin.get(name) match {
      case Some(null) => throw new ImplimentationErrorException(s"$name is not assigned yet")
      case Some(symbol) => symbol
      case None => throw new ImplimentationErrorException(s"$name is not builtin type")
    }
  }
}

