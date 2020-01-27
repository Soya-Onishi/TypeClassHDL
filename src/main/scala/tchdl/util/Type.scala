package tchdl.util

import tchdl.ast.Expression
import scala.collection.immutable

trait Type {
  def name: String
  def namespace: Vector[String]
  def declares: Map[String, Symbol]
  def tpeType: TpeType
  def tpeClass: TpeClass

  def returnType: Type
}

case class DeclaredType(
  name: String,
  namespace: Vector[String],
  hardwareParam: Vector[Symbol],
  typeParam: Vector[Symbol],
  declares: Map[String, Symbol],
  tpeType: TpeType,
  tpeClass: TpeClass,
) extends Type {
  def returnType: Type = this
}

case class MethodType(
  args: Vector[RefType],
  returnType: RefType
) extends Type {
  lazy val name: String = {
    val argTypeNames = args.map(_.name).mkString(", ")
    s"($argTypeNames) -> ${returnType.name}"
  }

  val namespace: Vector[String] = Vector()
  val declares = returnType.declares
  val tpeType = TpeType.Method
  val tpeClass = TpeClass.Software
}

case class RefType(
  origin: DeclaredType,
  hardwareParam: Vector[Expression],
  typeParam: Vector[RefType]
) extends Type {
  val name: String = origin.name
  val namespace: Vector[String] = origin.namespace
  val declares: Map[String, Symbol] = origin.declares
  val tpeType: TpeType = origin.tpeType
  def tpeClass: TpeClass = ???

  def returnType: Type = this
}

sealed trait TpeType
object TpeType {
  case object Module extends TpeType
  case object Struct extends TpeType
  case object Enum extends TpeType
  case object Class extends TpeType
  case object Interface extends TpeType
  case object Implement extends TpeType
  case object Method extends TpeType
  case object TypeParam extends TpeType
}

sealed trait TpeClass
object TpeClass {
  case object Software extends TpeClass
  case object Hardware extends TpeClass
  case object Module extends TpeClass
  case object Unknown extends TpeClass
  case class Mixed(set: immutable.Set[TpeClass]) extends TpeClass
  case class DependsOn(symbols: Vector[Symbol]) extends TpeClass
}