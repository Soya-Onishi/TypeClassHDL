package tchdl.typecheck

import tchdl.ast._
import tchdl.util.TchdlException.ImplementationErrorException
import tchdl.util._

object ProcVerifier {
  def exec(c: CompilationUnit)(implicit global: GlobalData): Unit = {
    val procs = c.topDefs
      .collect{ case impl: ImplementClass => impl }
      .flatMap(_.components)
      .collect{ case proc: ProcDef => proc }
      .flatMap(_.blks)

    procs.foreach(verifyProcBlock)
  }

  def verifyProcBlock(procBlock: ProcBlock)(implicit global: GlobalData): Unit = {
    val result = intoBlock(procBlock.blk) match {
      case None => Left(Error.ControlFlowNotExhaustive(procBlock.blk, procBlock.blk.position))
      case Some(Right(())) => Right(())
      case Some(Left(err)) => Left(err)
    }

    result.left.foreach(global.repo.error.append)
  }

  def intoExpr(expr: Expression): Option[Either[Error, Unit]] = expr match {
    case block: Block => intoBlock(block)
    case ifExpr: IfExpr => intoIfExpr(ifExpr)
    case matchExpr: Match => intoMatchExpr(matchExpr)
    case _: Relay => Right(()).some
    case _: Return => Right(()).some
    case _ => None
  }

  def intoBlock(blk: Block): Option[Either[Error, Unit]] = {
    val elems = blk.elems.collect{ case e: Expression => e }.map(intoExpr)
    val last = intoExpr(blk.last)
    val exprs = elems :+ last
    val (lefts, rights) = exprs.flatten.partitionMap(identity)

    if(rights.nonEmpty) Right(()).some
    else {
      if(lefts.isEmpty) None
      else Left(Error.MultipleErrors(lefts: _*)).some
    }
  }

  def intoIfExpr(ifExpr: IfExpr): Option[Either[Error, Unit]] = {
    val conseq = intoExpr(ifExpr.conseq)
    val alt = ifExpr.alt.flatMap(intoExpr)

    (conseq, alt) match {
      case (None, None) => None
      case (Some(l @ Left(_)), None) => l.some
      case (Some(Right(_)), None) => Left(Error.ControlFlowNotExhaustive(ifExpr, ifExpr.position)).some
      case (None, Some(_)) => Left(Error.ControlFlowNotExhaustive(ifExpr, ifExpr.position)).some
      case (Some(Right(_)), Some(Right(_))) => Right(()).some
      case (Some(l @ Left(_)), Some(Right(_))) => l.some
      case (Some(Left(l0)), Some(Left(l1))) => Left(Error.MultipleErrors(l0, l1)).some
    }
  }

  def intoMatchExpr(matchExpr: Match): Option[Either[Error, Unit]] = {
    val caseOpts = matchExpr.cases
      .map(_.exprs.collect{ case e: Expression => e }.map(intoExpr))
      .map{ exprs =>
        val (lefts, rights) = exprs.flatten.partitionMap(identity)
        if(rights.nonEmpty) Right(()).some
        else {
          if(lefts.isEmpty) None
          else Left(Error.MultipleErrors(lefts: _*)).some
        }
      }

    val allNone = caseOpts.forall(_.isEmpty)
    val hasNone = caseOpts.exists(_.isEmpty)
    val cases = caseOpts.collect{ case Some(c) => c }
    val hasLeft = cases.exists(_.isLeft)
    val hasRight = cases.exists(_.isRight)
    val allRight = cases.forall(_.isRight)

    lazy val r0 = cases.collect{ case Left(err) => err }.combine(errs => Error.MultipleErrors(errs: _*)).some
    lazy val r1 = Left(Error.ControlFlowNotExhaustive(matchExpr, matchExpr.position)).some

    if(allNone) None
    else if(hasLeft && hasNone) r0
    else if(hasRight && !allRight) r1
    else if(allRight) Right(()).some
    else throw new ImplementationErrorException("control flow must not reach here")
  }
}
