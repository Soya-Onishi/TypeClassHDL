package tchdl.util

import tchdl.ast._
import tchdl.backend._

import scala.reflect.runtime.universe.TypeTag

sealed trait Report {
  private val stackTrace = {
    (new Exception).getStackTrace.map(_.toString)
  }

  def debugString: String = {
    s"""
       |error: ${this.toString}
       |stacktrace:
       |  ${stackTrace.mkString("\n  ")}
       |""".stripMargin
  }

}
sealed trait Error extends Report
sealed trait Warning extends Report
sealed trait Info extends Report

object Error {
  case class TypeMismatch(expect: Type, actual: Type) extends Error
  case class SymbolNotFound(name: String) extends Error
  case object SelfTypeNotFound extends Error
  case class OperationNotFound(op: Operation) extends Error

  case class ParameterLengthMismatch(expect: Int, actual: Int) extends Error
  case class TypeParameterLengthMismatch(expect: Int, actual: Int) extends Error
  case class HardParameterLengthMismatch(expect: Int, actual: Int) extends Error
  case class PatternLengthMismatch(expect: Int, actual: Int) extends Error

  case class LiteralOnTarget(lit: HPExpr) extends Error
  case class EqAndOthersInSameBound(eqs: Vector[RangeExpr], others: Vector[RangeExpr]) extends Error
  case class ReferMethodAsNormal(symbol: Symbol.MethodSymbol) extends Error
  case class ReferMethodAsStatic(symbol: Symbol.MethodSymbol) extends Error
  case object RequireTypeTree extends Error
  case class RequireSpecificType(actual: Type.RefType, candidates: Type.RefType*) extends Error
  case class RequireModuleType(actual: Type.RefType) extends Error
  case class RequireHardwareType(actual: Type.RefType) extends Error
  case class RequireSymbol[Require <: Symbol : TypeTag](actual: Symbol) extends Error
  case class RequireFlag(require: Modifier, actual: Symbol) extends Error
  case class RequireStateSpecify(candidates: Vector[Symbol.StateSymbol]) extends Error

  case object RejectSelfType extends Error
  case object RejectHigherKind extends Error
  case object RejectTPFromSelf extends Error
  case object RejectPackage extends Error
  case class RejectEntityTypeFromLookup(symbol: Symbol.TypeSymbol) extends Error
  case class RejectTypeParam[From <: Symbol : TypeTag]() extends Error
  case class RejectHeapType(tpe: Type.RefType) extends Error

  case object RejectPolyParams extends Error
  case class NoNeedTypeParameter(method: Type.MethodType) extends Error
  case class NotMeetBound(tpe: Type, constraints: Vector[Type]) extends Error
  case class NotMeetHPBound(require: HPBound, caller: Option[HPBound]) extends Error
  case class NotMeetPartialTPBound(target: Type.RefType, require: Type.RefType) extends Error
  case class ValueNotMeetHPBound(value: Int, require: HPBound) extends Error
  case class NotEnoughHPBound(require: HPBound) extends Error
  case class ExcessiveHPBound(remains: Vector[HPBound]) extends Error
  case class NotEnoughTPBound(remains: TPBound) extends Error
  case class ExcessiveTPBound(remains: Vector[TPBound]) extends Error
  case object UsingSelfOutsideClass extends Error
  case object UsingSelfInsideStatic extends Error

  case class InvalidFormatForType(expr: Expression) extends Error
  case class InvalidFormatForModuleConstruct(expr: Expression) extends Error
  case class CannotUseStaticSelect(tree: StaticSelect) extends Error
  case class CannotUseCast(tree: CastType) extends Error

  case object FinishOutsideStage extends Error
  case object GotoOutsideState extends Error
  case object RelayOutsideStage extends Error
  case object ReturnOutsideStage extends Error

  case class DefinitionNameConflict(name: String) extends Error
  case class ImplementInterfaceConflict(impl0: ImplementInterfaceContainer, impl1: ImplementInterfaceContainer) extends Error
  case class ImplementClassConflict(impl0: ImplementClassContainer, impl1: ImplementClassContainer) extends Error
  case class ImplementMethodInterfaceNotHas(method: Symbol.MethodSymbol, interface: Symbol.InterfaceSymbol) extends Error
  case class RequireImplementMethod(require: Symbol.MethodSymbol) extends Error
  case class RequireImplementType(require: Symbol.TypeSymbol) extends Error
  case class AmbiguousSymbols(symbols: Vector[Symbol]) extends Error
  case class AmbiguousTypeParam(symbol: Symbol.TypeParamSymbol) extends Error
  case class AmbiguousHardwareParam(symbol: Symbol.HardwareParamSymbol) extends Error
  case object AttachTPToPackageSymbol extends Error
  case class InvalidTypeForHP(tpe: Type.RefType) extends Error
  case class TryDivisionByZero(expr: HPExpr) extends Error
  case class RangeAlreadyAssigned[T <: RangeExpr : TypeTag](value: Int) extends Error
  case class ImplTargetTypeMismatch(impl: ImplementContainer, actual: Type.RefType) extends Error
  case class RequireParentOrSiblingIndicator(construct: ConstructClass) extends Error
  case class RejectParentOrSiblingIndicator(construct: ConstructModule) extends Error
  case class TryToConstructInterface(construct: Construct) extends Error
  case class InvalidModifier(expect: Vector[Modifier], actual: Modifier) extends Error
  case class ImplementModuleComponentInStruct(tpe: Type.RefType) extends Error
  case class TryImplTraitByModule(impl: ImplementInterface) extends Error
  case class TryImplInterfaceByStruct(impl: ImplementInterface) extends Error
  case class TypeParameterMustHasConsistency(bounds: Vector[Type.RefType]) extends Error
  case class ModifierMismatch(expect: Modifier, actual: Modifier) extends Error

  case class ConstructEnumForm(tpe: Type.RefType) extends Error

  case class CallInterfaceFromInternal(method: Symbol.MethodSymbol) extends Error
  case class CallPrivate(method: Symbol.MethodSymbol) extends Error
  case class CallInvalid(method: Symbol.MethodSymbol) extends Error
  case class CallInterfaceMustBeDirect(prefix: Type.RefType) extends Error
  case class ReferPrivate(field: Symbol.TermSymbol) extends Error
  case class ReadOutputFromInner(field: Symbol.TermSymbol) extends Error
  case class ReadInputFromOuter(field: Symbol.TermSymbol) extends Error
  case class WriteInputFromInner(field: Symbol.TermSymbol) extends Error
  case class WriteOutputFromOuter(field: Symbol.TermSymbol) extends Error

  case class InvalidLHSForm(tree: Expression) extends Error

  case class MustNotCastFromTrait(from: Type.RefType) extends Error
  case class MustCastToTrait(to: Type.RefType) extends Error
  case class CannotCast(from: Type.RefType, to: Type.RefType) extends Error

  case class CyclicModuleInstantiation(module: BackendType, route: Vector[BackendType]) extends Error

  case class NotExhaustiveEnum(remains: Vector[Symbol.EnumMemberSymbol]) extends Error
  case class CannotUseBitLitForSWPattern(tpe: Type) extends Error

  case class RequireCastToLookup(tpe: Type.RefType) extends Error

  case class RequireLiteral(actual: AST) extends Error

  case class TopModuleHasNoImpl(tpe: Type.RefType) extends Error

  case class MultipleErrors(errs: Error*) extends Error
  case object DummyError extends Error
}


