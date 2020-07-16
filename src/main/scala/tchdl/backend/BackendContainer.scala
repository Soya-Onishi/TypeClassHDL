package tchdl.backend

import tchdl.util._
import scala.collection.immutable.ListMap

trait BackendContainer {
  def toFirrtlString: String
}

case class ModuleContainer(
  tpe: BackendType,
  hps: Map[String, HPElem],
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
  def empty(tpe: BackendType, hps: Map[String, HPElem]): ModuleContainer =
    ModuleContainer(tpe, hps, Vector.empty, Vector.empty, Vector.empty, Vector.empty)
}

case class MethodContainer(
  label: MethodLabel,
  hparams: ListMap[String, BackendType],
  params: ListMap[String, BackendType],
  code: Vector[ast.Stmt],
  ret: ast.Expr,
  retTpe: BackendType
) extends BackendContainer {
  def activeName: String = label.activeName
  def retName: String = label.retName

  lazy val toFirrtlString: String = label.toString
}

case class StageContainer(
  label: StageLabel,
  params: ListMap[String, BackendType],
  states: Vector[StateContainer],
  code: Vector[ast.Stmt],
  ret: BackendType
) extends BackendContainer {
  def activeName: String = label.activeName
  def retName: String = label.retName
  def stateName: String = label.stateName

  lazy val toFirrtlString: String = label.toString
}

case class StateContainer (
  label: StateLabel,
  params: ListMap[String, BackendType],
  code: Vector[ast.Stmt]
) extends BackendContainer {
  lazy val toFirrtlString: String = label.toString
}

case class FieldContainer(
  flag: Modifier,
  label: FieldLabel,
  code: Vector[ast.Stmt],
  ret: Option[ast.Expr],
  tpe: BackendType
) extends BackendContainer {
  override def toFirrtlString: String = label.toString
}

case class AlwaysContainer (
  symbol: Symbol.AlwaysSymbol,
  code: Vector[ast.Stmt]
) extends BackendContainer {
  override def toFirrtlString: String = symbol.name
}