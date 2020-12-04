package tchdl.backend

import tchdl.util._
import scala.collection.immutable.ListMap

trait BackendContainer {
  def toFirrtlString: String
}

case class ModuleContainer(
  tpe: BackendType,
  bodies: Vector[ModuleContainerBody],
  isNeedElaborate: Boolean
) extends BackendContainer {
  lazy val toFirrtlString = tpe.toFirrtlString
}

case class ModuleContainerBody(
  interface: Option[BackendType],
  hps: Map[String, HPElem],
  interfaces: Vector[MethodContainer],
  stages: Vector[StageContainer],
  always: Vector[AlwaysContainer],
  fields: Vector[FieldContainer],
  procs: Vector[ProcContainer],
) {
  def addInterface(interface: MethodContainer): ModuleContainerBody =
    this.copy(interfaces = this.interfaces :+ interface)

  def addStage(stage: StageContainer): ModuleContainerBody =
    this.copy(stages = this.stages :+ stage)

  def addAlways(always: AlwaysContainer): ModuleContainerBody =
    this.copy(always = this.always :+ always)

  def addField(field: FieldContainer): ModuleContainerBody =
    this.copy(fields = this.fields :+ field)

  def addProc(proc: ProcContainer): ModuleContainerBody =
    this.copy(procs = this.procs :+ proc)
}

object ModuleContainerBody {
  def empty(hps: Map[String, HPElem]): ModuleContainerBody =
    ModuleContainerBody(None, hps, Vector.empty, Vector.empty, Vector.empty, Vector.empty, Vector.empty)
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

case class ProcContainer (
  label: ProcLabel,
  default: Vector[ast.Stmt],
  defaultRet: ast.Expr,
  blks: Vector[ProcBlockContainer],
  ret: BackendType
) extends BackendContainer {
  lazy val toFirrtlString: String = label.toString
}

case class ProcBlockContainer (
  label: ProcBlockLabel,
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