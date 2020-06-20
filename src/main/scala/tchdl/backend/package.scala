package tchdl

import tchdl.ast._
import tchdl.util._

package object backend {
  case class StructureNode(
    module: Type.RefType,
    impl: Option[ImplementClassContainer],
    children: Vector[StructureNode]
  )

  case class ConcreteMethod(
    origin: Symbol.MethodSymbol,
    hpTable: Map[Symbol.HardwareParamSymbol, HPExpr],
    tpTable: Map[Symbol.TypeParamSymbol, Type.RefType],
    params: Vector[Type.RefType],
    process: Block
  )

  def searchTree[T <: Definition](symbol: Symbol): T = ???
}
