package tchdl.util

trait LookupResultContainer
case class StageResult(
  stage: Symbol.StageSymbol,
  stageTpe: Type.MethodType,
  hpTable: HPTable,
  tpTable: TPTable
) extends LookupResultContainer

case class ProcResult(
  proc: Symbol.ProcSymbol,
  retTpe: Type.RefType,
  hpTable: HPTable,
  tpTable: TPTable
) extends LookupResultContainer