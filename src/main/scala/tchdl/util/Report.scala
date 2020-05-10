package tchdl.util

import tchdl.ast._

sealed trait Report
sealed trait Error extends Report
sealed trait Warning extends Report
sealed trait Info extends Report

object Error {
  case class TypeMissmatch(expect: Type, actual: Type) extends Error
  case class SymbolNotFound(name: String) extends Error
  case class SymbolIsType(name: String) extends Error
  case class SymbolIsTerm(name: String) extends Error
  case class SetBoundForDifferentOwner(expect: Symbol, actual: Symbol) extends Error
  case class ParameterLengthMismatch(expect: Int, actual: Int) extends Error
  case class TypeParameterLengthMismatch(expect: Int, actual: Int) extends Error
  case class HardParameterLengthMismatch(expect: Int, actual: Int) extends Error
  case object RequireType extends Error
  case object RequireTypeParameter extends Error
  case class RequireStructOrModuleSymbol(name: String) extends Error
  case class RequireMethodType(actual: Type) extends Error
  case class RequireBooleanType(actual: Type) extends Error
  case class RequireTypeParamSymbol(name: String) extends Error
  case class RequireStateSymbol(name: String) extends Error
  case class RequireStageSymbol(name: String) extends Error
  case class RequireInterfaceSymbol(name: String) extends Error
  case object RejectSelfType extends Error
  case object RejectHigherKind extends Error
  case class NoNeedTypeParameter(method: Type.MethodType) extends Error
  case class NotMeetBound(tpe: Type, constraints: Vector[Type]) extends Error
  case object UsingSelfOutsideClass extends Error
  case class InvalidFormatForType(expr: Expression) extends Error
  case object FinishOutsideStage extends Error
  case object GotoOutsideState extends Error
  case object RelayOutsideStage extends Error
  case class DefinitionNameConflict(name: String) extends Error
  case class ImplementConflict() extends Error
  case class AmbiguousSymbols(symbols: Vector[Symbol]) extends Error

  case class MultipleErrors(errs: Seq[Error]) extends Error
  case object DummyError extends Error
}

object Reporter {
  private var errors = Vector.empty[Error]

  def appendError(err: Error): Unit = err match {
    case Error.MultipleErrors(errs) => errs.foreach(appendError)
    case err => errors = err +: errors
  }
  def errorCounts: Int = errors.length
}


