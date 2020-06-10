package tchdl.util

import tchdl.ast._
import tchdl.typecheck.{ImplementContainer, ImplementClassContainer, ImplementInterfaceContainer}
import tchdl.util.TchdlException.ImplementationErrorException
import scala.reflect.ClassTag
import scala.reflect.runtime.universe.TypeTag

sealed abstract class Symbol(__tpe: Type, __flag: Modifier) {
  def path: NameSpace
  def visibility: Visibility

  def name: String = path.name.get

  private var isAlreadyReferenced = false
  protected var _tpe: Type = __tpe
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

  override def hashCode(): Int = this.getClass.hashCode + this.path.hashCode

  def asTypeSymbol: Symbol.TypeSymbol = this.asInstanceOf[Symbol.TypeSymbol]
  def asTermSymbol: Symbol.TermSymbol = this.asInstanceOf[Symbol.TermSymbol]
  def asClassTypeSymbol: Symbol.ClassTypeSymbol = this.asInstanceOf[Symbol.ClassTypeSymbol]
  def asInterfaceSymbol: Symbol.InterfaceSymbol = this.asInstanceOf[Symbol.InterfaceSymbol]
  def asTypeParamSymbol: Symbol.TypeParamSymbol = this.asInstanceOf[Symbol.TypeParamSymbol]
  def asImplementSymbol: Symbol.ImplementSymbol = this.asInstanceOf[Symbol.ImplementSymbol]
  def asHardwareParamSymbol: Symbol.HardwareParamSymbol = this.asInstanceOf[Symbol.HardwareParamSymbol]
  def asMethodSymbol: Symbol.MethodSymbol = this.asInstanceOf[Symbol.MethodSymbol]

  def isTypeSymbol: Boolean = this.isInstanceOf[Symbol.TypeSymbol]
  def isTypeParamSymbol: Boolean = this.isInstanceOf[Symbol.TypeParamSymbol]
  def isEntityTypeSymbol: Boolean = this.isInstanceOf[Symbol.EntityTypeSymbol]
  def isFieldTypeSymbol: Boolean = this.isInstanceOf[Symbol.FieldTypeSymbol]
  def isMethodSymbol: Boolean = this.isInstanceOf[Symbol.MethodSymbol]
  def isInterfaceSymbol: Boolean = this.isInstanceOf[Symbol.InterfaceSymbol]
}

trait HasImpls {
  import scala.collection.mutable

  type ImplType <: ImplementContainer

  private val _impls = mutable.Map[Int, ImplType]()

  def appendImpl(implTree: ImplType#TreeType, impl: ImplType): Unit = _impls(implTree.id) = impl
  def removeImpl(id: Int): Unit = _impls.remove(id)
  def impls: Vector[ImplType] = _impls.values.toVector
}

trait HasParams {
  private var hardwareParam: Vector[Symbol.HardwareParamSymbol] = Vector.empty
  private var typeParam: Vector[Symbol.TypeParamSymbol] = Vector.empty
  def setHPs(hps: Vector[Symbol.HardwareParamSymbol]): Unit = hardwareParam = hps
  def setTPs(tps: Vector[Symbol.TypeParamSymbol]): Unit = typeParam = tps
  def hps: Vector[Symbol.HardwareParamSymbol] = hardwareParam
  def tps: Vector[Symbol.TypeParamSymbol] = typeParam

  private var bound: Option[Vector[Bound]] = None
  def tpBound: Vector[TPBound] = bound.getOrElse(Vector.empty).collect{ case b: TPBound => b }
  def hpBound: Vector[HPBound] = bound.getOrElse(Vector.empty).collect{ case b: HPBound => b }
  def setBound(set: Vector[Bound]): Unit = bound match {
    case None => bound = Some(set)
    case Some(_) => throw new ImplementationErrorException("bounds are already set")
  }
}

object Symbol {
  abstract class TypeSymbol(tpe: Type, flags: Modifier) extends Symbol(tpe, flags) with HasParams
  abstract class EntityTypeSymbol(tpe: Type, flags: Modifier) extends TypeSymbol(tpe, flags) with HasImpls
  abstract class ClassTypeSymbol(tpe: Type, flags: Modifier) extends EntityTypeSymbol(tpe, flags) {
    override type ImplType = ImplementClassContainer
  }

  class StructSymbol(
    val path: NameSpace,
    val visibility: Visibility,
    flags: Modifier,
    tpe: Type
  ) extends ClassTypeSymbol(tpe, flags)

  object StructSymbol {
    def apply(
      name: String,
      path: NameSpace,
      visibility: Visibility,
      flags: Modifier,
      tpe: Type
    ): StructSymbol =
      new StructSymbol(path.appendName(name), visibility, flags, tpe)
  }

  class ModuleSymbol(
    val path: NameSpace,
    val visibility: Visibility,
    flags: Modifier,
    tpe: Type
  ) extends ClassTypeSymbol(tpe, flags)

  object ModuleSymbol {
    def apply(
      name: String,
      path: NameSpace,
      visibility: Visibility,
      flags: Modifier,
      tpe: Type
    ): ModuleSymbol =
      new ModuleSymbol(path.appendName(name), visibility, flags, tpe)
  }

  class InterfaceSymbol(
    val path: NameSpace,
    val visibility: Visibility,
    flags: Modifier,
    tpe: Type,
  ) extends EntityTypeSymbol(tpe, flags) {
    override type ImplType = ImplementInterfaceContainer
  }

  object InterfaceSymbol {
    def apply(
      name: String,
      path: NameSpace,
      visibility: Visibility,
      flags: Modifier,
      tpe: Type
    ): InterfaceSymbol =
      new InterfaceSymbol(path.appendName(name), visibility, flags, tpe)
  }

  class TypeParamSymbol(val path: NameSpace, tpe: Type) extends TypeSymbol(tpe, Modifier.NoModifier) {
    override val visibility: Visibility = Visibility.Private

    private var _bounds: Option[Vector[Type.RefType]] = None
    def setBounds(bounds: Vector[Type.RefType]): Unit =
      if(_bounds.isDefined) throw new ImplementationErrorException("bounds already assigned")
      else _bounds = Some(bounds)
    def getBounds: Vector[Type.RefType] = _bounds.getOrElse(Vector.empty)
  }

  object TypeParamSymbol {
    def apply(name: String, path: NameSpace, tpe: Type): TypeParamSymbol =
      new TypeParamSymbol(path.appendName(name), tpe)
  }

  class FieldTypeSymbol(
    val path: NameSpace,
    tpe: Type,
    flags: Modifier
  ) extends TypeSymbol(tpe, flags) {
    override val visibility: Visibility = Visibility.Public
  }

  abstract class TermSymbol(tpe: Type, flags: Modifier) extends Symbol(tpe, flags)

  class VariableSymbol(
    val path: NameSpace,
    val visibility: Visibility,
    flags: Modifier,
    tpe: Type
  ) extends TermSymbol(tpe, flags)

  object VariableSymbol {
    def apply(name: String, path: NameSpace, visibility: Visibility, flags: Modifier, tpe: Type): VariableSymbol =
      new VariableSymbol(path.appendName(name), visibility, flags, tpe)
  }

  class HardwareParamSymbol(val path: NameSpace, tpe: Type) extends TermSymbol(tpe, Modifier.NoModifier) {
    val visibility: Visibility = Visibility.Private
  }

  object HardwareParamSymbol {
    def apply(name: String, path: NameSpace, tpe: Type): HardwareParamSymbol =
      new HardwareParamSymbol(path.appendName(name), tpe)
  }

  class MethodSymbol(
    val path: NameSpace,
    val visibility: Visibility,
    flags: Modifier,
    tpe: Type
  ) extends TermSymbol(tpe, flags) with HasParams

  object MethodSymbol {
    def apply(
      name: String,
      path: NameSpace,
      visibility: Visibility,
      flags: Modifier,
      tpe: Type
    ): MethodSymbol =
      new MethodSymbol(path.appendName(name), visibility, flags, tpe)
  }

  class AlwaysSymbol(val path: NameSpace) extends TermSymbol(Type.NoType, Modifier.NoModifier) {
    override val visibility: Visibility = Visibility.Private
  }

  object AlwaysSymbol {
    def apply(name: String, path: NameSpace): AlwaysSymbol =
      new AlwaysSymbol(path.appendName(name))
  }

  class StageSymbol(val path: NameSpace, tpe: Type) extends TermSymbol(tpe, Modifier.NoModifier) {
    override val visibility: Visibility = Visibility.Private
  }

  object StageSymbol {
    def apply(name: String, path: NameSpace, tpe: Type): StageSymbol =
      new StageSymbol(path.appendName(name), tpe)
  }

  class StateSymbol(val path: NameSpace) extends Symbol(Type.NoType, Modifier.NoModifier){
    override val visibility: Visibility = Visibility.Private
  }

  object StateSymbol {
    def apply(name: String, path: NameSpace): StateSymbol =
      new StateSymbol(path.appendName(name))
  }

  class ImplementSymbol(
    val treeID: Int,
    val path: NameSpace,
  ) extends Symbol(null, Modifier.NoModifier) with HasParams {
    override val visibility: Visibility = Visibility.Public

    override def setTpe(tpe: Type): Unit =
      throw new ImplementationErrorException("ImplementSymbol does not allow refer to setTpe")
    override def tpe: Type =
      throw new ImplementationErrorException("ImplementSymbol does not allow refer to tpe")

    override def hashCode(): Int = treeID.hashCode() + path.hashCode()
  }

  object ImplementSymbol {
    def apply(
      id: Int,
      path: NameSpace,
    ): ImplementSymbol = {
      new ImplementSymbol(id, path.appendName(ImplementId.id().toString))
    }
  }

  class PackageSymbol(
    val path: NameSpace,
  ) extends Symbol(null, Modifier.NoModifier) {
    import scala.collection.mutable

    override def name: String = path.pkgName.last
    override val visibility: Visibility = Visibility.Public

    private val scope = Scope.empty
    def lookup[T <: Symbol : ClassTag : TypeTag](name: String): LookupResult[T] = scope.lookup(name) match {
      case Some(symbol: T) => LookupResult.LookupSuccess(symbol)
      case Some(symbol) => LookupResult.LookupFailure(Error.RequireSymbol[T](symbol))
      case None => LookupResult.LookupFailure(Error.SymbolNotFound(name))
    }
    def append(symbol: Symbol): Either[Error, Unit] = scope.append(symbol)

    private val _context = mutable.Map[String, Context.RootContext]()
    def context: Map[String, Context.RootContext] = _context.toMap
    def lookupCtx(filename: String): Option[Context.RootContext] = _context.get(filename)
    def appendCtx(filename: String, ctx: Context.RootContext): Unit =
      _context.get(filename) match {
        case None => _context(filename) = ctx
        case Some(_) =>
          val msg = "context is appended with key(filename) which is already assigned here"
          throw new ImplementationErrorException(msg)
      }
  }

  object PackageSymbol {
    def apply(parent: PackageSymbol, name: String): PackageSymbol = {
      val pkg = parent.path.pkgName :+ name
      new PackageSymbol(NameSpace(pkg, Vector.empty, None))
    }

    def apply(name: String): PackageSymbol =
      new PackageSymbol(NameSpace(Vector(name), Vector.empty, None))
  }

  object RootPackageSymbol extends PackageSymbol(NameSpace.empty) {
    override def lookupCtx(name: String): Option[Context.RootContext] = {
      val msg = "try to lookup context in RootPackageSymbol"
      throw new ImplementationErrorException(msg)
    }

    override def appendCtx(filename: String, ctx: Context.RootContext): Unit = {
      val msg = "try to append context in RootPackageSymbol"
      throw new ImplementationErrorException(msg)
    }

    def search(pkgName: Vector[String]): Either[String, Symbol.PackageSymbol] = {
      pkgName.foldLeft[Either[String, Symbol.PackageSymbol]](Right(this)){
        case (Left(name), _) => Left(name)
        case (Right(symbol), name) =>
          symbol.lookup[Symbol.PackageSymbol](name)
            .toEither
            .map(Right.apply)
            .getOrElse(Left(name))
      }
    }
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
    "Int" -> null,
    "String" -> null,
    "Unit" -> null,
    "Bit" -> null,
    "Num" -> null,
    "Str" -> null,
  )

  def builtInNames: Vector[String] = builtin.keys.toVector

  def appendBuiltin(symbol: Symbol.TypeSymbol): Unit = {
    builtin.get(symbol.name) match {
      case None => throw new ImplementationErrorException(s"${symbol.name} is not a builtin type")
      case Some(null) => builtin(symbol.name) = symbol
      case Some(_) => throw new ImplementationErrorException(s"${symbol.name} is already assigned")
    }
  }

  def lookupBuiltin(name: String): Symbol.TypeSymbol = {
    builtin.get(name) match {
      case Some(null) => throw new ImplementationErrorException(s"$name is not assigned yet")
      case Some(symbol) => symbol
      case None => throw new ImplementationErrorException(s"$name is not builtin type")
    }
  }
}

