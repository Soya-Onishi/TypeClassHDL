package tchdl.util

import tchdl.ast._
import tchdl.util.TchdlException._
import tchdl.backend._

import scala.collection.mutable
import java.nio.file.{Path, Paths}

abstract class GlobalData {
  val repo: Reporter = new Reporter
  val rootPackage: Symbol.RootPackageSymbol = new Symbol.RootPackageSymbol
  val cache: TypedTreeCache = new TypedTreeCache

  val builtin = new {
    val types: BuiltInTypes = new BuiltInTypes
    val interfaces: BuiltInInterfaces = new BuiltInInterfaces
    val operators: BuiltInOperators = new BuiltInOperators
  }

  val buffer = new {
    val traits: SymbolBuffer[Symbol.InterfaceSymbol] = new SymbolBuffer[Symbol.InterfaceSymbol] {}
    val clazz: SymbolBuffer[Symbol.ClassTypeSymbol] = new SymbolBuffer[Symbol.ClassTypeSymbol] {}
  }

  protected val backendFields: mutable.Map[BackendType, Map[String, BackendType]] = mutable.Map()

  def appendFields(tpe: BackendType, fields: Map[String, BackendType]): Unit = {
    backendFields(tpe) = fields
  }

  def lookupFields(tpe: BackendType)(implicit global: GlobalData): Map[String, BackendType] =
    backendFields.get(tpe) match {
      case Some(field) => field
      case None =>
        val hpTable = (tpe.symbol.hps zip tpe.hargs).toMap
        val tpTable = (tpe.symbol.tps zip tpe.targs).toMap
        val fields = tpe.symbol.tpe.declares.toMap.map {
          case (name, symbol) => name -> toBackendType(symbol.tpe.asRefType, hpTable, tpTable)
        }

        this.appendFields(tpe, fields)
        fields
    }

  private var procIDMax: Int = 0
  private val procIDMap: mutable.Map[Symbol.ProcSymbol, Int] = mutable.Map.empty
  def getID(symbol: Symbol.ProcSymbol): Int =
    procIDMap.get(symbol) match {
      case Some(id) => id
      case None =>
        procIDMap(symbol) = procIDMax
        val ret = procIDMax
        procIDMax += 1
        ret
    }

  val config: CLConfig
  def compilationUnits: Seq[CompilationUnit] = throw new ImplementationErrorException("Compilation Units not assigned yet")

  def assignCompilationUnits(cus: Seq[CompilationUnit]): GlobalData = {
    val _repo = repo
    val _rootPackage = rootPackage
    val _cache = cache
    val _builtin = builtin
    val _buffer = buffer
    val _command = config

    new GlobalData {
      override val repo = _repo
      override val rootPackage = _rootPackage
      override val cache = _cache
      override val builtin = _builtin
      override val buffer = _buffer
      override val config = _command
      override val compilationUnits = cus
    }
  }
}

object GlobalData {
  def apply(conf: CLConfig): GlobalData =
    new GlobalData { override val config = conf }

  def apply(pkgName: Vector[String], module: TypeTree): GlobalData = {
    val conf = CLConfig(
      Vector.empty,
      pkgName,
      Some(module),
      Paths.get("out.v"),
      Paths.get("."),
      frontendOnly = false,
      outputFir = false,
    )

    new GlobalData {
      override val config = conf
    }
  }

  def apply(): GlobalData = {
    val conf = CLConfig(
      Vector.empty,
      Vector.empty,
      Option.empty,
      Paths.get("out.v"),
      Paths.get("."),
      frontendOnly = false,
      outputFir = false,
    )

    new GlobalData {
      override val config = conf
    }
  }
}

trait BuiltInSymbols[T <: Symbol] {
  import scala.collection.mutable
  protected val builtin: mutable.Map[String, T]

  def toMap: Map[String, T] = builtin.toMap
  def names: Vector[String] = builtin.keys.toVector
  def symbols: Vector[T] = {
    val symbols = builtin.values.toVector

    if(symbols.contains(null)) throw new ImplementationErrorException("BuiltIn types are not registered completely")
    else symbols
  }


  def append(symbol: T): Unit = {
    builtin.get(symbol.name) match {
      case None => throw new ImplementationErrorException(s"${symbol.name} is not a builtin symbol")
      case Some(null) => builtin(symbol.name) = symbol
      case Some(_) => throw new ImplementationErrorException(s"${symbol.name} is already assigned")
    }
  }

  def lookup(name: String): T = {
    builtin.get(name) match {
      case Some(null) => throw new ImplementationErrorException(s"$name is not assigned yet")
      case Some(symbol) => symbol
      case None => throw new ImplementationErrorException(s"$name is not builtin symbol")
    }
  }

  def lookupSafe(name: String): Option[T] = {
    builtin.get(name) match {
      case Some(null) => None
      case Some(symbol) => Some(symbol)
      case None => None
    }
  }
}

class BuiltInTypes extends BuiltInSymbols[Symbol.ClassTypeSymbol] {
  import scala.collection.mutable

  // There is null. However, this null will never go to outside of this builtin table.
  // because appendBuiltin and lookupBuiltin see whether Map's value is null or not, and
  // if it is null, methods address that case.
  protected val builtin: mutable.Map[String, Symbol.ClassTypeSymbol] = mutable.Map[String, Symbol.ClassTypeSymbol](
    "Int" -> null,
    "String" -> null,
    "Unit" -> null,
    "Bit" -> null,
    "Num" -> null,
    "Str" -> null,
    "Bool" -> null,
    "Vector" -> null,
    "Memory" -> null,
  )
}

class BuiltInInterfaces extends BuiltInSymbols[Symbol.InterfaceSymbol] {
  import scala.collection.mutable

  protected val builtin: mutable.Map[String, Symbol.InterfaceSymbol] = mutable.Map[String, Symbol.InterfaceSymbol](
    "HW" -> null,
    "Module" -> null,
  )
}

class BuiltInOperators extends BuiltInSymbols[Symbol.MethodSymbol] {
  import scala.collection.mutable

  protected val builtin: mutable.Map[String, Symbol.MethodSymbol] = mutable.Map[String, Symbol.MethodSymbol](
    "add" -> null,
    "sub" -> null,
    "mul" -> null,
    "div" -> null,
    "or"  -> null,
    "and" -> null,
    "xor" -> null,
    "shl" -> null,
    "shr" -> null,
    "dynShl" -> null,
    "dynShr" -> null,
    "equal" -> null,
    "notEqual" -> null,
    "greaterThan" -> null,
    "greaterEqual" -> null,
    "lessThan" -> null,
    "lessEqual" -> null,
    "not" -> null,
    "neg" -> null,
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

case class Command(
  filenames: Vector[String],
  topModulePkg: Vector[String],
  topModule: Option[TypeTree],
  stdlibDir: String,
  output: Option[String],
  outputDir: Option[Path],
)

object Command {
  def empty: Command = Command(Vector.empty, Vector.empty, Option.empty, "", None, None)
}