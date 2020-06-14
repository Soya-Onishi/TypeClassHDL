package tchdl.typecheck

import tchdl.ast._
import tchdl.util._

object TyperUtil {
  def verifyMethodDef(methodDef: MethodDef)(implicit ctx: Context.NodeContext, global: GlobalData): Either[Error, Symbol.MethodSymbol] = {
    def verifyHPTpes(hps: Vector[ValDef]): Either[Error, Unit] = {
      val hasError = hps.map(_.symbol.tpe).exists(_.isErrorType)

      if(hasError) Left(Error.DummyError)
      else Right(())
    }

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

    def verifyMethodTpe(tpe: Type): Either[Error, Type.MethodType] =
      tpe match {
        case Type.ErrorType => Left(Error.DummyError)
        case tpe: Type.MethodType => Right(tpe)
      }

    val methodSymbol = methodDef.symbol.asMethodSymbol
    val signatureCtx = Context(ctx, methodSymbol)
    signatureCtx.reAppend (
      methodSymbol.hps ++
        methodSymbol.tps: _*
    )

    val hpBoundTrees = methodDef.bounds.collect{ case b: HPBoundTree => b }
    val tpBoundTrees = methodDef.bounds.collect{ case b: TPBoundTree => b }

    for {
      _ <- verifyHPTpes(methodDef.hp)
      _ <- HPBound.verifyAllForms(hpBoundTrees)
      hpBounds = hpBoundTrees.map(HPBound.apply)
      (targetErrs, targets) = tpBoundTrees.view.map(_.target).map(TPBound.buildTarget).to(Vector).unzip
      (boundsErrs, bounds) = tpBoundTrees.view.map(_.bounds).map(TPBound.buildBounds).to(Vector).unzip
      errs = (targetErrs ++ boundsErrs).flatten
      _ <- if(errs.nonEmpty) Left(Error.MultipleErrors(errs: _*)) else Right(())
      tpBounds = (targets zip bounds).view
        .map{ case (t, bs) => (t.tpe.asRefType, bs.map(_.tpe.asRefType)) }
        .map{ case (t, bs) => TPBound(t, bs) }
        .to(Vector)
      _ = methodSymbol.setBound(hpBounds ++ tpBounds)
      _ <- verifyTPBoundType(methodSymbol)(signatureCtx)
      _ <- verifyMethodTpe(methodSymbol.tpe)
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
