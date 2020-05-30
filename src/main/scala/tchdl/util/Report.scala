package tchdl.util

import tchdl.ast._
import scala.reflect.ClassTag
import scala.reflect.runtime.universe.TypeTag

sealed trait Report
sealed trait Error extends Report
sealed trait Warning extends Report
sealed trait Info extends Report

object Error {
  case class TypeMissmatch(expect: Type, actual: Type) extends Error
  case class SymbolNotFound(name: String) extends Error
  case class PackageNotFound(name: String) extends Error
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
  case class RequirePackageSymbol(name: String) extends Error
  case class RequireSpecificType(requires: Vector[Type], actual: Type) extends Error
  case class RequireSymbol[Require <: Symbol : TypeTag](actual: Symbol) extends Error
  case class RequireFlag(require: Modifier, actual: Symbol) extends Error
  case object RejectSelfType extends Error
  case object RejectHigherKind extends Error
  case object RejectTPFromSelf extends Error
  case object RejectPackage extends Error
  case class RejectEntityTypeFromLookup(symbol: Symbol.TypeSymbol) extends Error
  case class RejectTypeParam[From <: Symbol : TypeTag]() extends Error
  case class NoNeedTypeParameter(method: Type.MethodType) extends Error
  case class NotMeetBound(tpe: Type, constraints: Vector[Type]) extends Error
  case object UsingSelfOutsideClass extends Error
  case class InvalidFormatForType(expr: Expression) extends Error
  case object FinishOutsideStage extends Error
  case object GotoOutsideState extends Error
  case object RelayOutsideStage extends Error
  case class DefinitionNameConflict(name: String) extends Error
  case class ImplementInterfaceConflict(interface: Type.RefType, target: Type.RefType) extends Error
  case class ImplementClassConflict(target: Type.RefType) extends Error
  case class AmbiguousSymbols(symbols: Vector[Symbol]) extends Error
  case object AttachTPToPackageSymbol extends Error
  case class InvalidTypeForHP(tpe: Type.RefType) extends Error

  case class MultipleErrors(errs: Error*) extends Error {
    def apply(errs: Vector[Error]): MultipleErrors = {
      new MultipleErrors(errs: _*)
    }
  }
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


