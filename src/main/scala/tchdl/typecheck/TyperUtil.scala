package tchdl.typecheck

import tchdl.util._

object TyperUtil {
  def verifyTPBoundType(symbol: Symbol with HasParams)(implicit ctx: Context.NodeContext): Either[Error, Unit] = {
    def verifyEachBounds(hpBounds: Vector[HPBound], tpBounds: Vector[TPBound])(implicit ctx: Context.NodeContext): Either[Error, Unit] = {
      val (hpErrs, _) = hpBounds.map(HPBound.verifyMeetBound(_, ctx.hpBounds)).partitionMap(identity)
      val (tpErrs, _) = tpBounds.map(TPBound.verifyMeetBound(_, ctx.hpBounds, ctx.tpBounds)).partitionMap(identity)
      val errs = hpErrs ++ tpErrs

      if(errs.isEmpty) Right(())
      else Left(Error.MultipleErrors(errs: _*))
    }

    val tpBounds = symbol.tpBound
    val results = tpBounds.flatMap{ tpBound => tpBound.bounds.map{
      bound =>
        val symbol = bound.origin.asInterfaceSymbol
        val hpTable = (symbol.hps zip bound.hardwareParam).toMap
        val tpTable = (symbol.tps zip bound.typeParam).toMap
        val replacedHPBound = HPBound.swapBounds(symbol.hpBound, hpTable)
        val replacedTPBound = TPBound.swapBounds(symbol.tpBound, hpTable, tpTable)

        verifyEachBounds(replacedHPBound, replacedTPBound)
    }}

    val (errs, _) = results.partitionMap(identity)

    if(errs.isEmpty) Right(())
    else Left(Error.MultipleErrors(errs: _*))
  }
}
