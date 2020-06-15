package tchdl.typecheck

import tchdl.ast._
import tchdl.util._

object TyperUtil {
  def verifyMethodValidity(methodDef: MethodDef)(implicit ctx: Context.NodeContext, global: GlobalData): Either[Error, Symbol.MethodSymbol] = {
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

    def verifyMethodTpe: Either[Error, Unit] = {
      val paramTpes = methodDef.params.map(_.symbol.tpe)
      val retTpe = methodDef.retTpe.tpe

      (paramTpes :+ retTpe).map {
        case Type.ErrorType => Left(Error.DummyError)
        case _ => Right(())
      }.combine(errs => Error.MultipleErrors(errs: _*))
    }

    val methodSymbol = methodDef.symbol.asMethodSymbol
    val signatureCtx = Context(ctx, methodSymbol)
    signatureCtx.reAppend (
      methodSymbol.hps ++
      methodSymbol.tps: _*
    )

    for {
      _ <- verifyTPBoundType(methodSymbol)(signatureCtx)
      _ <- verifyMethodTpe
    } yield methodSymbol
  }

  def verifyStageDef(stageDef: StageDef)(implicit ctx: Context.NodeContext, global: GlobalData): Either[Error, Symbol.StageSymbol] = {
    val stageSymbol = stageDef.symbol.asStageSymbol
    stageSymbol.tpe match {
      case Type.ErrorType => Left(Error.DummyError)
      case _: Type.RefType => Right(stageSymbol)
    }
  }
}
