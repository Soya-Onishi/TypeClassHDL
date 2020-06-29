package tchdl.backend

import tchdl.util._
import scala.collection.immutable.ListMap

trait BackendContainer {
  def toFirrtlString: String
}

case class ModuleContainer(
  tpe: BackendType,
  interfaces: Vector[MethodContainer],
  stages: Vector[StageContainer],
  always: Vector[AlwaysContainer],
  fields: Vector[FieldContainer]
) extends BackendContainer {
  def addInterface(interface: MethodContainer): ModuleContainer =
    this.copy(interfaces = this.interfaces :+ interface)

  def addStage(stage: StageContainer): ModuleContainer =
    this.copy(stages = this.stages :+ stage)

  def addAlways(always: AlwaysContainer): ModuleContainer =
    this.copy(always = this.always :+ always)

  def addField(field: FieldContainer): ModuleContainer =
    this.copy(fields = this.fields :+ field)

  lazy val toFirrtlString = tpe.toFirrtlString
}

object ModuleContainer {
  def empty(tpe: BackendType): ModuleContainer =
    ModuleContainer(tpe, Vector.empty, Vector.empty, Vector.empty, Vector.empty)
}

case class MethodContainer(
  label: MethodLabel,
  hargs: ListMap[String, BackendType],
  args: ListMap[String, BackendType],
  code: Vector[ast.Stmt],
  ret: ast.Expr
) extends BackendContainer {
  def activeName: String = label.toString + "$active"
  def retName: String = label.toString + "$ret"

  lazy val toFirrtlString: String = label.toString
}

case class StageContainer(
  label: StageLabel,
  args: ListMap[String, BackendType],
  states: Vector[StateContainer],
  code: Vector[ast.Stmt]
) extends BackendContainer {
  lazy val toFirrtlString: String = label.symbol.name
}

case class StateContainer (
  symbol: Symbol.StateSymbol,
  stageFirrtlString: String,
  code: Vector[ast.Stmt]
) extends BackendContainer {
  lazy val toFirrtlString: String = {
    val name = symbol.name

    stageFirrtlString + "$" + name
  }
}

case class FieldContainer(
  flag: Modifier,
  symbol: Symbol.VariableSymbol,
  code: Vector[ast.Stmt],
  ret: Option[ast.Expr],
  tpe: BackendType
) extends BackendContainer {
  override def toFirrtlString: String = symbol.name
}

case class AlwaysContainer (
  symbol: Symbol.AlwaysSymbol,
  code: Vector[ast.Stmt]
) extends BackendContainer {
  override def toFirrtlString: String = symbol.name
}