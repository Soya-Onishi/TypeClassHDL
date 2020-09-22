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
  case class TypeMismatch(expect: Type, actual: Type, pos: Position) extends Error
  case class SymbolNotFound(name: String, pos: Position) extends Error
  case class SelfTypeNotFound(pos: Position) extends Error

  case class ParameterLengthMismatch(expect: Int, actual: Int, pos: Position) extends Error
  case class TypeParameterLengthMismatch(expect: Int, actual: Int, pos: Position) extends Error
  case class HardParameterLengthMismatch(expect: Int, actual: Int, pos: Position) extends Error
  case class PatternLengthMismatch(expect: Int, actual: Int, pos: Position) extends Error

  case class ReferMethodAsNormal(symbol: Symbol.MethodSymbol, pos: Position) extends Error
  case class ReferMethodAsStatic(symbol: Symbol.MethodSymbol, pos: Position) extends Error
  case class RequireTypeTree(pos: Position) extends Error
  case class RequireSpecificType(actual: Type.RefType, requires: Seq[Type.RefType], pos: Position) extends Error
  case class RequireModuleType(actual: Type.RefType, pos: Position) extends Error
  case class RequirePointerOrHWType(actual: Type.RefType, pos: Position) extends Error
  case class RequireSymbol[Require <: Symbol : TypeTag](actual: Symbol, pos: Position) extends Error
  case class RequireFlag(require: Modifier, actual: Symbol, pos: Position) extends Error
  case class RequireStateSpecify(candidates: Vector[Symbol.StateSymbol], pos: Position)extends Error
  case class RequirePointerTypeAsProcRet(tpe: Type.RefType, pos: Position) extends Error
  case class RequireHWAsPointer(tpe: Type.RefType, pos: Position) extends Error

  case class RejectHeapType(tpe: Type.RefType, pos: Position) extends Error
  case class RejectPointerType(tpe: TypeTree, pos: Position) extends Error

  case class HPConstraintSetMultitime(target: HPExpr, pos: Position) extends Error
  case class NotMeetBound(tpe: Type, constraints: Vector[Type], pos: Position) extends Error
  case class NotMeetHPBound(require: HPBound, caller: Option[HPBound], pos: Position) extends Error
  case class LiteralOnTarget(lit: Literal, pos: Position) extends Error
  case class HPBoundNotEqualExpr(expect: HPExpr, actual: HPExpr, pos: Position) extends Error
  case class HPBoundNotDeriveEqualConst(expr: HPExpr, pos: Position) extends Error
  case class HPBoundEqualConstNotMatch(expect: Int, actual: Int, pos: Position) extends Error
  case class HPBoundOutOfRange(expr: HPExpr, expect: (IInt, IInt), actual: (IInt, IInt), pos: Position) extends Error
  case class HPBoundRangeCross(max: IInt, min: IInt, pos: Position) extends Error
  case class HPBoundConstraintMismatch(expect: HPConstraint, actual: HPConstraint, pos: Position) extends Error
  case class NotEnoughHPBound(require: HPBound, pos: Position) extends Error
  case class ExcessiveHPBound(remains: Vector[HPBound], pos: Position) extends Error

  case class NotMeetPartialTPBound(target: Type.RefType, require: Type.RefType, pos: Position) extends Error
  case class NotEnoughTPBound(remains: TPBound, pos: Position) extends Error
  case class ExcessiveTPBound(remains: Vector[TPBound], pos: Position) extends Error

  case class UsingSelfOutsideClass(pos: Position) extends Error
  case class UsingSelfInsideStatic(pos: Position) extends Error

  case class InvalidFormatForType(expr: Expression, pos: Position) extends Error
  case class InvalidFormatForModuleConstruct(expr: Expression, pos: Position) extends Error
  case class CannotUseStaticSelect(tree: StaticSelect, pos: Position) extends Error
  case class CannotUseCast(tree: CastType, pos: Position) extends Error

  case class FinishOutsideStage(pos: Position) extends Error
  case class GotoOutsideState(pos: Position) extends Error
  case class RelayOutsideStageOrProc(pos: Position) extends Error
  case class RelayWithStateInProc(pos: Position) extends Error
  case class ReturnOutsideStage(pos: Position) extends Error
  case class ReturnOutsideProcBlock(pos: Position) extends Error

  case class DefinitionNameConflict(name: String, pos: Position) extends Error
  case class ImplementInterfaceConflict(impl0: ImplementInterfaceContainer, impl1: ImplementInterfaceContainer, pos0: Position, pos: Position) extends Error
  case class ImplementClassConflict(impl0: ImplementClassContainer, impl1: ImplementClassContainer, pos0: Position, pos1: Position) extends Error
  case class ImplementMethodInterfaceNotHas(method: Symbol.MethodSymbol, interface: Symbol.InterfaceSymbol, methodPos: Position) extends Error
  case class RequireImplementMethod(require: Symbol.MethodSymbol, implPos: Position) extends Error
  case class RequireImplementType(require: Symbol.TypeSymbol, implPos: Position) extends Error
  case class AmbiguousMethods(symbols: Vector[Symbol], pos: Position) extends Error
  case class AmbiguousTypeParam(symbol: Seq[Symbol.TypeParamSymbol], callPos: Position) extends Error
  case class AmbiguousHardwareParam(symbol: Seq[Symbol.HardwareParamSymbol], callPos: Position) extends Error

  case class ImplTargetTypeMismatch(impl: ImplementContainer, actual: Type.RefType, implPos: Position) extends Error
  case class RequireParentOrSiblingIndicator(construct: ConstructClass, pos: Position) extends Error
  case class RejectParentOrSiblingIndicator(construct: ConstructModule, pos: Position) extends Error
  case class TryToConstructInterface(construct: Construct, pos: Position) extends Error
  case class InvalidModifier(expect: Vector[Modifier], actual: Modifier, pos: Position) extends Error
  case class ImplementModuleComponentInStruct(tpe: Type.RefType, pos: Position) extends Error
  case class TryImplTraitByModule(impl: ImplementInterface, pos: Position) extends Error
  case class TryImplInterfaceByStruct(impl: ImplementInterface, pos: Position) extends Error
  case class TypeParameterMustHasConsistency(bounds: Vector[Type.RefType], pos: Position) extends Error
  case class ModifierMismatch(expect: Modifier, actual: Modifier, pos: Position) extends Error

  case class ConstructEnumForm(tpe: Type.RefType, pos: Position) extends Error

  case class CallInterfaceFromInternal(method: Symbol.MethodSymbol, pos: Position) extends Error
  case class CallPrivate(method: Symbol.MethodSymbol, pos: Position) extends Error
  case class CallInvalid(method: Symbol.MethodSymbol, pos: Position) extends Error
  case class CallInterfaceMustBeDirect(prefix: Type.RefType, pos: Position) extends Error
  case class ReferPrivate(field: Symbol.TermSymbol, pos: Position) extends Error
  case class ReadOutputFromInner(field: Symbol.TermSymbol, pos: Position) extends Error
  case class ReadInputFromOuter(field: Symbol.TermSymbol, pos: Position) extends Error
  case class WriteInputFromInner(field: Symbol.TermSymbol, pos: Position) extends Error
  case class WriteOutputFromOuter(field: Symbol.TermSymbol, pos: Position) extends Error

  case class InvalidLHSForm(tree: Expression, pos: Position) extends Error

  case class MustNotCastFromTrait(from: Type.RefType, pos: Position) extends Error
  case class MustCastToTrait(to: Type.RefType, pos: Position) extends Error
  case class CannotCast(from: Type.RefType, to: Type.RefType, pos: Position) extends Error
  case class RequireCastToLookup(tpe: Type.RefType, pos: Position) extends Error

  case class CyclicModuleInstantiation(module: BackendType, route: Vector[BackendType], pos: Position) extends Error
  case class RequireLiteral(actual: AST) extends Error

  case class MultipleErrors(errs: Error*) extends Error
  case object DummyError extends Error
}


