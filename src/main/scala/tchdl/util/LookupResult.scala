package tchdl.util

import tchdl.typecheck.ImplementInterfaceContainer

sealed trait LookupResult

object LookupResult {
  case class LookupSuccess(symbol: Symbol) extends LookupResult
  case class LookupFailure(err: Error) extends LookupResult
}