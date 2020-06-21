package tchdl.util

import tchdl.ast._
import tchdl.util.TchdlException._

class GlobalData {
  val repo: Reporter = new Reporter
  val rootPackage: Symbol.RootPackageSymbol = new Symbol.RootPackageSymbol
  val cache: TypedTreeCache = new TypedTreeCache

  val builtin = new {
    val types: BuiltInTypes = new BuiltInTypes
    val interfaces: BuiltInInterfaces = new BuiltInInterfaces
  }

  val buffer = new {
    val traits: SymbolBuffer[Symbol.InterfaceSymbol] = new SymbolBuffer[Symbol.InterfaceSymbol] {}
    val clazz: SymbolBuffer[Symbol.ClassTypeSymbol] = new SymbolBuffer[Symbol.ClassTypeSymbol] {}
  }

  val command = new {
    var topModulePkg: Vector[String] = Vector.empty
    var topModule: Option[TypeTree] = Option.empty[TypeTree]
  }
}

trait BuiltInSymbols[T <: Symbol] {
  import scala.collection.mutable
  protected val builtin: mutable.Map[String, T]

  def names: Vector[String] = builtin.keys.toVector
  def symbols: Vector[T] = {
    val symbols = builtin.values.toVector

    if(symbols.contains(null)) throw new ImplementationErrorException("BuiltIn types are not registered completely")
    else symbols
  }


  def append(symbol: T): Unit = {
    builtin.get(symbol.name) match {
      case None => throw new ImplementationErrorException(s"${symbol.name} is not a builtin type")
      case Some(null) => builtin(symbol.name) = symbol
      case Some(_) => throw new ImplementationErrorException(s"${symbol.name} is already assigned")
    }
  }

  def lookup(name: String): T = {
    builtin.get(name) match {
      case Some(null) => throw new ImplementationErrorException(s"$name is not assigned yet")
      case Some(symbol) => symbol
      case None => throw new ImplementationErrorException(s"$name is not builtin type")
    }
  }
}

class BuiltInTypes extends BuiltInSymbols[Symbol.EntityTypeSymbol] {
  import scala.collection.mutable

  // There is null. However, this null will never go to outside of this builtin table.
  // because appendBuiltin and lookupBuiltin see whether Map's value is null or not, and
  // if it is null, methods address that case.
  protected val builtin: mutable.Map[String, Symbol.EntityTypeSymbol] = mutable.Map[String, Symbol.EntityTypeSymbol](
    "Int" -> null,
    "String" -> null,
    "Unit" -> null,
    "Bit" -> null,
    "Num" -> null,
    "Str" -> null,
    "Bool" -> null,
  )
}

class BuiltInInterfaces extends BuiltInSymbols[Symbol.InterfaceSymbol] {
  import scala.collection.mutable

  protected val builtin: mutable.Map[String, Symbol.InterfaceSymbol] = mutable.Map[String, Symbol.InterfaceSymbol](
    "Add" -> null,
    "Sub" -> null,
    "Mul" -> null,
    "Div" -> null,
    "Eq" -> null,
    "HW" -> null,
    "Module" -> null,
  )
}

class TypedTreeCache {
  import scala.collection.mutable

  private val cache = mutable.Map[Int, AST]()

  def get(tree: AST): Option[AST] = cache.get(tree.id)
  def get(id: Int): Option[AST] = cache.get(id)
  def set(tree: AST): Unit = cache(tree.id) = tree
}

trait Reports[T] {
  protected var _elems = Vector.empty[T]

  def elems: Vector[T] = _elems
  def counts: Int = _elems.length
  def append(elem: T): Unit
}

class Reporter {
  val error: Reports[Error] = new Reports[Error] {
    override def append(err: Error): Unit = {
      def flatten(errs: Seq[Error]): Vector[Error] = {
        errs.toVector.flatMap {
          case err: Error.MultipleErrors => flatten(err.errs)
          case Error.DummyError => Vector()
          case err => Vector(err)
        }
      }

      err match {
        case err: Error.MultipleErrors => this._elems = flatten(err.errs) ++ this._elems
        case Error.DummyError => // nothing to do
        case err => this._elems = err +: this._elems
      }
    }
  }
}

trait SymbolBuffer[T] {
  import scala.collection.mutable

  private val _symbols = mutable.HashSet[T]()

  def symbols: Vector[T] = _symbols.toVector
  def append(symbol: T): Unit = _symbols += symbol
}