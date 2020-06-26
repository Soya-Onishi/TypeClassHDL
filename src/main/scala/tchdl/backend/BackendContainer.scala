package tchdl.backend

import tchdl.util._

trait BackendContainer

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
}

object ModuleContainer {
  def empty(tpe: BackendType): ModuleContainer =
    ModuleContainer(tpe, Vector.empty, Vector.empty, Vector.empty, Vector.empty)
}

case class MethodContainer(
  label: MethodLabel,
  hargs: Vector[ast.Term.Variable],
  args: Vector[ast.Term.Variable],
  code: Vector[ast.BackendIR]
) extends BackendContainer

case class StageContainer(
  label: StageLabel,
  args: Vector[ast.Term.Variable],
  states: Vector[StateContainer],
  code: Vector[ast.BackendIR]
) extends BackendContainer

case class StateContainer (
  symbol: Symbol.StateSymbol,
  code: Vector[ast.BackendIR]
) extends BackendContainer

case class FieldContainer(
  flag: Modifier,
  symbol: Symbol.VariableSymbol,
  code: Vector[ast.BackendIR]
) extends BackendContainer

case class AlwaysContainer (
  symbol: Symbol.AlwaysSymbol,
  code: Vector[ast.BackendIR]
) extends BackendContainer