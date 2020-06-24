package tchdl

import tchdl.ast._
import tchdl.util._

import scala.reflect.ClassTag
import scala.reflect.runtime.universe.TypeTag

package object backend {
  class BuiltModule (
    val id: Int,
    val module: Type.RefType,
    val impl: Option[ImplementClassContainer],
    val childIDs: Vector[Int]
  )

  object BuiltModule {
    private var _id = 0

    def apply(module: Type.RefType, impl: Option[ImplementClassContainer], childIDs: Vector[Int]): BuiltModule = {
      val id = _id
      _id = _id + 1

      new BuiltModule(id, module, impl, childIDs)
    }
  }

  case class ConcreteMethod(
    origin: Symbol.MethodSymbol,
    hpTable: Map[Symbol.HardwareParamSymbol, HPExpr],
    tpTable: Map[Symbol.TypeParamSymbol, Type.RefType],
    params: Vector[Type.RefType],
    process: Block
  )

  def searchTree[T <: Definition](id: Int)(implicit global: GlobalData, ev0: ClassTag[T], ev1: TypeTag[T]): Option[T] = global.cache.get(id) match {
    case None => None
    case Some(tree: T) => Some(tree)
    case Some(_) => None
  }

  trait HPElem
  object HPElem {
    case class Num(n: Int) extends HPElem
    case class Str(s: String) extends HPElem
  }

  case class BackendType(symbol: Symbol.TypeSymbol, hargs: Vector[HPElem], targs: Vector[BackendType])

}
