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
  case object RequireType extends Error
  case object RequireTypeParameter extends Error
  case class RequireMethodType(actual: Type) extends Error
  case class RequireBooleanType(actual: Type) extends Error
  case class RequireTypeParamSymbol(name: String) extends Error
  case class RequireStateSymbol(name: String) extends Error
  case class RequireStageSymbol(name: String) extends Error
  case class NoNeedTypeParameter(method: Type.MethodType) extends Error
  case class NotMeedBounds(tpe: Type, constraints: Vector[Type]) extends Error
  case object UsingSelfOutsideClass extends Error
  case class InvalidFormatForType(expr: Expression) extends Error
  case object FinishOutsideStage extends Error
  case object GotoOutsideState extends Error
  case object RelayOutsideStage extends Error
  case class DefinitionNameConflict(name: String) extends Error
  case class ImplementConflict() extends Error
}


