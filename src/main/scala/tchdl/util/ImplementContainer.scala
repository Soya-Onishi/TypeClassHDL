package tchdl.util

import tchdl.ast._
import tchdl.util.TchdlException.ImplementationErrorException

import scala.reflect.ClassTag
import scala.reflect.runtime.universe.TypeTag

abstract class ImplementContainer {
  type TreeType <: Definition

  val ctx: Context.RootContext
  val targetType: Type.RefType
  val scope: Scope
  val symbol: Symbol.ImplementSymbol
  val id: Int
  val typeParam: Vector[Symbol.TypeParamSymbol]
  val hardwareParam: Vector[Symbol.HardwareParamSymbol]

  final def lookup[T <: Symbol : ClassTag : TypeTag](name: String): Option[T] =
    scope.lookup(name).collect{ case symbol: T => symbol }

  final override def hashCode(): Int = super.hashCode()
  final override def equals(obj: Any): Boolean = obj match {
    case that: ImplementContainer => this.hashCode == that.hashCode
    case _ => false
  }
}

abstract class ImplementInterfaceContainer(
  val ctx: Context.RootContext,
  val targetInterface: Type.RefType,
  val targetType: Type.RefType,
  val scope: Scope
) extends ImplementContainer {
  override type TreeType = ImplementInterface
  override def toString: String = s"impl $targetInterface for $targetType"
}

object ImplementInterfaceContainer {
  def apply(
    implTree: ImplementInterface,
    ctx: Context.RootContext,
    interface: Type.RefType,
    tpe: Type.RefType,
    scope: Scope
  ): ImplementInterfaceContainer =
    new ImplementInterfaceContainer(ctx, interface, tpe, scope) {
      override val symbol: Symbol.ImplementSymbol = implTree.symbol.asImplementSymbol
      override val id: Int = implTree.id
      override val typeParam: Vector[Symbol.TypeParamSymbol] = implTree.tp.map(_.symbol.asTypeParamSymbol)
      override val hardwareParam: Vector[Symbol.HardwareParamSymbol] = implTree.hp.map(_.symbol.asHardwareParamSymbol)
    }

  def isConflict(impl0: ImplementInterfaceContainer, impl1: ImplementInterfaceContainer)(implicit global: GlobalData): Boolean = {
    // if tpe0 = Type[u32] and tpe1 = Type[T]
    // T -> None => T -> Some(u32)
    // if tpe0 = Type[T] and tpe1 = Type[u32]
    // T -> None => T -> None
    def assignTypes(
      tpe0: Type.RefType,
      tpe1: Type.RefType,
      table: Map[Symbol.TypeParamSymbol, Option[Type.RefType]]
    ): Option[Map[Symbol.TypeParamSymbol, Option[Type.RefType]]] = {
      (tpe0.origin, tpe1.origin) match {
        case (e0: Symbol.EntityTypeSymbol, e1: Symbol.EntityTypeSymbol) =>
          if(e0 != e1) None
          else {
            (tpe0.typeParam zip tpe1.typeParam)
              .foldLeft[Option[Map[Symbol.TypeParamSymbol, Option[Type.RefType]]]](Some(table)){
                case (Some(tab), (t0, t1)) => assignTypes(t0, t1, tab)
                case (None, _) => None
              }
          }
        case (_: Symbol.TypeParamSymbol, _: Symbol.EntityTypeSymbol) => Some(table)
        case (tp0: Symbol.TypeParamSymbol, tp1: Symbol.TypeParamSymbol) if tp0 == tp1 => Some(table)
        case (_, e1: Symbol.TypeParamSymbol) => table.get(e1) match {
          // if already assigned, these pair will not be conflict
          // like impl[T] Tr[T] for T and impl Tr[u32] for u64
          case Some(Some(_)) => Some(table)
          case Some(None) => Some(table.updated(e1, Some(tpe0)))
          case None => throw new ImplementationErrorException(s"table should have [${e1.name}] as key")
        }
      }
    }

    def unwrapSafety(table: Map[Symbol.TypeParamSymbol, Option[Type.RefType]]): Map[Symbol.TypeParamSymbol, Type.RefType] =
      table.collect { case (key, Some(value)) => key -> value }

    val table = (impl0.symbol.tps ++ impl1.symbol.tps).map(_ -> Option.empty[Type.RefType]).toMap
    val assignedTable = for {
      table <- assignTypes(impl0.targetInterface, impl1.targetInterface, table)
      table <- assignTypes(impl0.targetType, impl1.targetType, table)
      replacedInterface = impl1.targetInterface.replaceWithMap(Map.empty, unwrapSafety(table))
      replacedTarget = impl1.targetType.replaceWithMap(Map.empty, unwrapSafety(table))
      table <- assignTypes(replacedInterface, impl0.targetInterface, table)
      table <- assignTypes(replacedTarget, impl0.targetType, table)
      assignedTable = unwrapSafety(table)
    } yield assignedTable

    assignedTable match {
      case None => false
      case Some(table) =>
        def isMeetTPBounds: Boolean = {
          def verifyTPBound(
            hpBounds: Vector[HPBound],
            combinedTPBounds: Vector[TPBound],
            table: Map[Symbol.TypeParamSymbol, Type.RefType]
          ): Boolean = {
            val verified = table.collect { case (tp, tpe) if tpe.origin.isEntityTypeSymbol => tp -> tpe }
            val verifiedBounds = verified.toVector.map {
              case (tp, tpe) =>
                val bounds = combinedTPBounds.find(_.target.origin == tp).map(_.bounds).getOrElse(Vector.empty)
                val swappedBounds = bounds.map(_.replaceWithMap(Map.empty, verified))

                TPBound(tpe, swappedBounds)
            }

            verifiedBounds.forall {
              TPBound.verifyMeetBound(_, hpBounds, combinedTPBounds).isRight
            }
          }

          val table0 = table.collect{ case (key, value) if impl0.typeParam.contains(key) => key -> value }
          val table1 = table.collect{ case (key, value) if impl1.typeParam.contains(key) => key -> value }

          val combinedTPBounds = impl0.symbol.tpBound ++ impl1.symbol.tpBound
          verifyTPBound(impl0.symbol.hpBound, combinedTPBounds, table0) &&
            verifyTPBound(impl1.symbol.hpBound, combinedTPBounds, table1)
        }

        def isOverlapHPBounds(tpe0: Type.RefType, tpe1: Type.RefType, hpBound0: Vector[HPBound], hpBound1: Vector[HPBound]): Boolean = {
          if(tpe0.origin.isTypeParamSymbol || tpe1.origin.isTypeParamSymbol) true
          else {
            val isOverlapped = (tpe0.hardwareParam zip tpe1.hardwareParam).forall {
              case (hp0, hp1) =>
                def findRange(target: HPExpr, bounds: Vector[HPBound]): HPConstraint = target match {
                  case IntLiteral(value) => HPConstraint.Eqn(Vector(IntLiteral(value)))
                  case expr => bounds
                    .find(_.target.isSameExpr(expr))
                    .map(_.bound)
                    .getOrElse(HPConstraint.empty)
                }


                val range0 = findRange(hp0, hpBound0)
                val range1 = findRange(hp1, hpBound1)
                HPConstraint.isOverlapped(range0, range1, hpBound0, hpBound1)
            }

            isOverlapped && (tpe0.typeParam zip tpe1.typeParam).forall{
              case (t0, t1) => isOverlapHPBounds(t0, t1, hpBound0, hpBound1)
            }
          }
        }

        def isSameForm: Boolean = {
          def verifySameForm(tpe0: Type.RefType, tpe1: Type.RefType): Boolean = {
            def isRefTpeContainSecificTP(tpe: Type.RefType, tp: Symbol.TypeParamSymbol): Boolean = tpe.origin match {
              case referred: Symbol.TypeParamSymbol => referred == tp
              case _: Symbol.EntityTypeSymbol => tpe.typeParam.exists(isRefTpeContainSecificTP(_, tp))
            }

            (tpe0.origin, tpe1.origin) match {
              case (e0: Symbol.EntityTypeSymbol, e1: Symbol.EntityTypeSymbol) =>
                e0 == e1 && (tpe0.typeParam zip tpe1.typeParam).forall {
                  case (t0, t1) => verifySameForm(t0, t1)
                }
              case (_: Symbol.TypeParamSymbol, _: Symbol.TypeParamSymbol) => true
              case (tp: Symbol.TypeParamSymbol, _: Symbol.EntityTypeSymbol) => !isRefTpeContainSecificTP(tpe1, tp)
              case (_: Symbol.EntityTypeSymbol, tp: Symbol.TypeParamSymbol) => !isRefTpeContainSecificTP(tpe0, tp)
            }
          }

          lazy val implTarget0 = impl0.targetType.replaceWithMap(Map.empty, table)
          lazy val implTarget1 = impl1.targetType.replaceWithMap(Map.empty, table)
          lazy val implInterface0 = impl0.targetInterface.replaceWithMap(Map.empty, table)
          lazy val implInterface1 = impl1.targetInterface.replaceWithMap(Map.empty, table)

          verifySameForm(implTarget0, implTarget1) &&
          verifySameForm(implInterface0, implInterface1)
        }

        isSameForm &&
        isMeetTPBounds &&
        isOverlapHPBounds(impl0.targetType, impl1.targetType, impl0.symbol.hpBound, impl1.symbol.hpBound) &&
        isOverlapHPBounds(impl0.targetInterface, impl1.targetInterface, impl0.symbol.hpBound, impl1.symbol.hpBound)
    }
  }
}

abstract class ImplementClassContainer(
  val ctx: Context.RootContext,
  val targetType: Type.RefType,
  val scope: Scope
) extends ImplementContainer {
  override type TreeType = ImplementClass
  override def toString: String = s"impl $targetType"
}

object ImplementClassContainer {
  def apply(
    implTree: ImplementClass,
    ctx: Context.RootContext,
    tpe: Type.RefType,
    scope: Scope
  ): ImplementClassContainer =
    new ImplementClassContainer(ctx, tpe, scope) {
      override val symbol: Symbol.ImplementSymbol = implTree.symbol.asImplementSymbol
      override val id: Int = implTree.id
      override val typeParam: Vector[Symbol.TypeParamSymbol] = implTree.tp.map(_.symbol.asTypeParamSymbol)
      override val hardwareParam: Vector[Symbol.HardwareParamSymbol] = implTree.hp.map(_.symbol.asHardwareParamSymbol)
    }

  def isConflict(impl0: ImplementClassContainer, impl1: ImplementClassContainer)(implicit global: GlobalData): Boolean = {
    def buildTable(
      tpe0: Type.RefType,
      tpe1: Type.RefType,
      table: Map[Symbol.TypeParamSymbol, Option[Type.RefType]]
    ): Map[Symbol.TypeParamSymbol, Option[Type.RefType]] = {
      def update(
        key: Symbol.TypeParamSymbol,
        tpe: Type.RefType,
        table: Map[Symbol.TypeParamSymbol, Option[Type.RefType]]
      ): Map[Symbol.TypeParamSymbol, Option[Type.RefType]] =
        table.get(key) match {
          case None => throw new ImplementationErrorException(s"table should have ${key.name} as key")
          case Some(_) => table.updated(key, Some(tpe))
        }

      (tpe0.origin, tpe1.origin) match {
        case (e0: Symbol.EntityTypeSymbol, e1: Symbol.EntityTypeSymbol) =>
          if(e0 != e1) table
          else {
            (tpe0.typeParam zip tpe1.typeParam).foldLeft(table){
              case (tab, (t0, t1)) => buildTable(t0, t1, tab)
            }
          }
        case (tp: Symbol.TypeParamSymbol, _: Symbol.EntityTypeSymbol) => update(tp, tpe1, table)
        case (_: Symbol.EntityTypeSymbol, tp: Symbol.TypeParamSymbol) => update(tp, tpe0, table)
        case (tp0: Symbol.TypeParamSymbol, tp1: Symbol.TypeParamSymbol) => update(tp1, tpe0, update(tp0, tpe1, table))
      }
    }

    def unwrapTable(table: Map[Symbol.TypeParamSymbol, Option[Type.RefType]]): Map[Symbol.TypeParamSymbol, Type.RefType] =
      table.collect { case (key, Some(value)) => key -> value }

    def isSameForm(tpe0: Type.RefType, tpe1: Type.RefType): Boolean =
      (tpe0.origin, tpe1.origin) match {
        case (e0: Symbol.EntityTypeSymbol, e1: Symbol.EntityTypeSymbol) =>
          if(e0 != e1) false
          else (tpe0.typeParam zip tpe1.typeParam)
            .forall { case (t0, t1) => isSameForm(t0, t1) }
        case (_: Symbol.TypeParamSymbol, _: Symbol.TypeParamSymbol) => true
        case _ => throw new ImplementationErrorException("this pattern case should not be reached")
      }

    def hasSameNameMethod: Boolean = {
      val methods0 = impl0.scope.toMap.keys.toVector
      val methods1 = impl1.scope.toMap.keys.toVector

      methods1.exists(methods0.contains)
    }

    def isOverlapHPBounds(
      tpe0: Type.RefType,
      tpe1: Type.RefType,
      hpBounds0: Vector[HPBound],
      hpBounds1: Vector[HPBound]
    ): Boolean = {
      def findRange(target: HPExpr, bounds: Vector[HPBound]): HPConstraint =
        bounds
          .find(_.target.isSameExpr(target))
          .map(_.bound)
          .getOrElse(HPConstraint.empty)

      (tpe0.origin, tpe1.origin) match {
        case (_: Symbol.EntityTypeSymbol, _: Symbol.EntityTypeSymbol) =>
          val hpOverlapped = (tpe0.hardwareParam zip tpe1.hardwareParam).forall {
            case (hp0, hp1) =>
              val range0 = findRange(hp0, hpBounds0)
              val range1 = findRange(hp1, hpBounds1)
              HPConstraint.isOverlapped(range0, range1, hpBounds0, hpBounds1)
          }

          hpOverlapped && (tpe0.typeParam zip tpe1.typeParam).forall {
            case (t0, t1) => isOverlapHPBounds(t0, t1, hpBounds0, hpBounds1)
          }
        case _ => true
      }
    }

    def isMeetTPBounds(table: Map[Symbol.TypeParamSymbol, Type.RefType]): Boolean = {
      def verifyTPBound(
        hpBounds: Vector[HPBound],
        combinedTPBounds: Vector[TPBound],
        table: Map[Symbol.TypeParamSymbol, Type.RefType]
      ): Boolean = {
        val verified = table.collect { case (tp, tpe) if tpe.origin.isEntityTypeSymbol => tp -> tpe }
        val verifiedBounds = verified.toVector.map {
          case (tp, tpe) =>
            val bounds = combinedTPBounds.find(_.target.origin == tp).map(_.bounds).getOrElse(Vector.empty)
            val swappedBounds = bounds.map(_.replaceWithMap(Map.empty, verified))

            TPBound(tpe, swappedBounds)
        }

        verifiedBounds.forall {
          TPBound.verifyMeetBound(_, hpBounds, combinedTPBounds).isRight
        }
      }

      val table0 = table.collect{ case (key, value) if impl0.typeParam.contains(key) => key -> value }
      val table1 = table.collect{ case (key, value) if impl1.typeParam.contains(key) => key -> value }

      val combinedTPBounds = impl0.symbol.tpBound ++ impl1.symbol.tpBound

      verifyTPBound(impl0.symbol.hpBound, combinedTPBounds, table0) &&
      verifyTPBound(impl1.symbol.hpBound, combinedTPBounds, table1)
    }

    val table = unwrapTable(buildTable(
      impl0.targetType,
      impl1.targetType,
      (impl0.symbol.tps ++ impl1.symbol.tps).map(_ -> Option.empty[Type.RefType]).toMap
    ))

    val swappedTarget0 = impl0.targetType.replaceWithMap(Map.empty, table)
    val swappedTarget1 = impl1.targetType.replaceWithMap(Map.empty, table)

    isSameForm(swappedTarget0, swappedTarget1) &&
    hasSameNameMethod &&
    isOverlapHPBounds(impl0.targetType, impl1.targetType, impl0.symbol.hpBound, impl1.symbol.hpBound) &&
    isMeetTPBounds(table)
  }
}
