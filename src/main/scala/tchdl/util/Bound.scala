package tchdl.util

import tchdl.ast._
import tchdl.util.TchdlException.ImplementationErrorException

import scala.annotation.tailrec

trait Bound
object Bound {
  def verifyEachBounds(
    hpBounds: Vector[HPBound],
    tpBounds: Vector[TPBound],
    callerHPBound: Vector[HPBound],
    callerTPBound: Vector[TPBound],
    impl: ImplementContainer,
    target: Type.RefType
  )(implicit global: GlobalData): Either[Error, Unit] = {
    val (hpErrs, _) = hpBounds
      .map(HPBound.verifyMeetBound(_, callerHPBound))
      .partitionMap(identity)

    val (tpErrs, _) = tpBounds
      .map(TPBound.verifyMeetBound(_, callerHPBound, callerTPBound))
      .partitionMap(identity)

    val errs = hpErrs ++ tpErrs
    if (errs.isEmpty) Right(())
    else Left(Error.ImplTargetTypeMismatch(impl, target))
  }
}


class TPBound(
  val target: Type.RefType,
  val bounds: Vector[Type.RefType]
) extends Bound {
  override def equals(obj: Any): Boolean = obj match {
    case that: TPBound =>
      def forall(thisBounds: Vector[Type.RefType], thatBounds: Vector[Type.RefType]): Boolean =
        thatBounds.headOption match {
          case None => true
          case Some(head) => thisBounds.findRemain(_ =:= head) match {
            case (None, _) => false
            case (_, remains) => forall(remains, thatBounds.tail)
          }
        }
      this.target =:= that.target &&
      this.bounds.length == that.bounds.length &&
      forall(this.bounds, that.bounds)
    case _ => false
  }
}

object TPBound {
  def apply(bound: TPBoundTree): TPBound =
    new TPBound(
      bound.target.tpe.asRefType,
      bound.bounds.map(_.tpe.asRefType)
    )

  def apply(target: Type.RefType, bounds: Vector[Type.RefType]): TPBound =
    new TPBound(target, bounds)

  def buildTarget(target: TypeTree)(implicit ctx: Context.NodeContext, global: GlobalData): (Option[Error], TypeTree) =
    Type.buildType[Symbol.TypeParamSymbol](target)

  def buildBounds(bounds: Vector[TypeTree])(implicit ctx: Context.NodeContext, global: GlobalData): (Option[Error], Vector[TypeTree]) = {
    val (errs, tpes) = bounds.map(Type.buildType[Symbol.InterfaceSymbol]).unzip
    val err = errs.flatten match {
      case Vector() => None
      case errs => Some(Error.MultipleErrors(errs: _*))
    }

    (err, tpes)
  }

  def swapBounds(
    swapped: Vector[TPBound],
    hpTable: Map[Symbol.HardwareParamSymbol, HPExpr],
    tpTable: Map[Symbol.TypeParamSymbol, Type.RefType]
  ): Vector[TPBound] = {
    def swapHP(expr: HPExpr): HPExpr = expr match {
      case ident: Ident => hpTable(ident.symbol.asHardwareParamSymbol)
      case HPBinOp(op, left, right) => HPBinOp(op, swapHP(left), swapHP(right))
      case lit => lit
    }

    def swapTP(tpe: Type.RefType): Type.RefType = {
      lazy val swappedTP = tpe.typeParam.map(swapTP)
      lazy val swappedHP = tpe.hardwareParam.view.map(swapHP).map(_.sort).toVector
      tpe.origin match {
        case _: Symbol.EntityTypeSymbol =>
          Type.RefType(tpe.origin, swappedHP, swappedTP)
        case tp: Symbol.TypeParamSymbol =>
          tpTable.getOrElse(tp, throw new ImplementationErrorException(s"table should have ${tp.name}"))
      }
    }

    def swapBound(bound: TPBound): TPBound = {
      val target = swapTP(bound.target)
      val bounds = bound.bounds.map(swapTP)

      TPBound(target, bounds)
    }

    swapped.map(swapBound)
  }

  def verifyMeetBound(
    swapped: TPBound,
    callerHPBound: Vector[HPBound],
    callerTPBound: Vector[TPBound]
  )(implicit global: GlobalData): Either[Error, Unit] =
    swapped.target.origin match {
      case _: Symbol.EntityTypeSymbol => verifyEntityTarget(swapped, callerHPBound, callerTPBound)
      case _: Symbol.TypeParamSymbol => verifyTypeParamTarget(swapped, callerHPBound, callerTPBound)
    }

  private def verifyEntityTarget(
    tpBound: TPBound,
    callerHPBound: Vector[HPBound],
    callerTPBound: Vector[TPBound]
  )(implicit global: GlobalData): Either[Error, Unit] = {
    lazy val hwSymbol = global.builtin.interfaces.lookup("HW")
    lazy val modSymbol = global.builtin.interfaces.lookup("Module")

    def verify(impl: ImplementInterfaceContainer, bound: Type.RefType): Boolean = {
      val initHPTable = impl.hardwareParam.map(_ -> Option.empty[HPExpr]).toMap
      val initTPTable = impl.typeParam.map(_ -> Option.empty[Type.RefType]).toMap
      val targets = Vector(impl.targetType, impl.targetInterface)
      val referer = Vector(tpBound.target, bound)

      val result = for {
        _ <- Type.RefType.verifySuperSets(referer, targets)
        hpTable <- Type.RefType.assignHPTable(initHPTable, referer, targets)
        tpTable <- Type.RefType.assignTPTable(initTPTable, referer, targets)
        swappedHPBounds = HPBound.swapBounds(impl.symbol.hpBound, hpTable)
        swappedTPBounds = TPBound.swapBounds(impl.symbol.tpBound, hpTable, tpTable)
        _ <- {
          val (hpErrs, _) = swappedHPBounds
            .map(HPBound.verifyMeetBound(_, callerHPBound))
            .partitionMap(identity)

          val (tpErrs, _) = swappedTPBounds
            .map(TPBound.verifyMeetBound(_, callerHPBound, callerTPBound))
            .partitionMap(identity)

          val errs = hpErrs ++ tpErrs
          if(errs.isEmpty) Right(())
          else Left(Error.MultipleErrors(errs: _*))
        }
      } yield ()

      result.isRight
    }

    def isHardwareType(tpe: Type.RefType): Boolean = {
      val builtinSymbols = global.builtin.types.symbols
      tpe.origin match {
        case _: Symbol.ModuleSymbol => false
        case _: Symbol.InterfaceSymbol => false
        case tp: Symbol.TypeParamSymbol => callerTPBound.find(_.target.origin == tp) match {
          case None => false
          case Some(tpBound) =>
            val hardwareInterface = Type.RefType(global.builtin.interfaces.lookup("HW"))
            tpBound.bounds.exists(_ =:= hardwareInterface)
        }
        case struct: Symbol.StructSymbol if struct == global.builtin.types.lookup("Bit") => true
        case struct: Symbol.StructSymbol if builtinSymbols.contains(struct) => false
        case struct: Symbol.StructSymbol if struct.tpe.declares.toMap.isEmpty => false
        case struct: Symbol.StructSymbol =>
          val hpTable = (struct.hps zip tpe.hardwareParam).toMap
          val tpTable = (struct.tps zip tpe.typeParam).toMap
          val fields = struct.tpe.declares.toMap.values.toVector
          val fieldTpes = fields.map(_.tpe.asRefType.replaceWithMap(hpTable, tpTable))
          fieldTpes.forall(isHardwareType)
      }
    }

    def isModuleType(tpe: Type.RefType): Boolean = tpe.origin match {
      case _: Symbol.ModuleSymbol => true
      case _: Symbol.InterfaceSymbol => false
      case tp: Symbol.TypeParamSymbol => callerTPBound.find(_.target.origin == tp) match {
        case None => false
        case Some(tpBound) =>
          val moduleInterface = Type.RefType(global.builtin.interfaces.lookup("Module"))
          tpBound.bounds.exists(_ =:= moduleInterface)
      }
    }


    val results = tpBound.bounds.map { bound => bound.origin match {
      case hw if hw == hwSymbol =>
        if(isHardwareType(tpBound.target)) Right(())
        else Left(Error.NotMeetPartialTPBound(tpBound.target, bound))
      case mod if mod == modSymbol =>
        if(isModuleType(tpBound.target)) Right(())
        else Left(Error.NotMeetPartialTPBound(tpBound.target, bound))
      case interface: Symbol.InterfaceSymbol =>
        val impls = interface.impls
        val isValid = impls.exists(impl => verify(impl, bound))

        if(isValid) Right(())
        else Left(Error.NotMeetPartialTPBound(tpBound.target, bound))
    }}

    val (errs, _) = results.partitionMap(identity)

    if(errs.isEmpty) Right(())
    else Left(Error.MultipleErrors(errs: _*))
  }

  private def verifyTypeParamTarget(
    swappedTPBound: TPBound,
    callerHPBound: Vector[HPBound],
    callerTPBound: Vector[TPBound]
  ): Either[Error, Unit] = {
    callerTPBound.find(_.target.origin == swappedTPBound.target.origin) match {
      case Some(bound) =>
        val results = swappedTPBound.bounds.map{
          calledBound =>
            if(bound.bounds.exists(_ =:= calledBound)) Right(())
            else Left(Error.NotMeetPartialTPBound(swappedTPBound.target, calledBound))
        }

        val (errs, _) = results.partitionMap(identity)
        if(errs.isEmpty) Right(())
        else Left(Error.MultipleErrors(errs: _*))
      case None =>
        val isValid = swappedTPBound.bounds.isEmpty
        lazy val errs = swappedTPBound
          .bounds
          .map(Error.NotMeetPartialTPBound(swappedTPBound.target, _))

        if(isValid) Right(())
        else Left(Error.MultipleErrors(errs: _*))
    }

    /*
    val results = swappedTPBound.bounds.map { bound =>
      callerTPBound.find(_.target.origin == swappedTPBound.target.origin) match {
        case Some(bound) =>
      }
      val interface = bound.origin.asInterfaceSymbol
      val hpTable = (interface.hps zip bound.hardwareParam).toMap
      val tpTable = (interface.tps zip bound.typeParam).toMap
      val swappedHPBounds = HPBound.swapBounds(interface.hpBound, hpTable)
      val swappedTPBounds = TPBound.swapBounds(interface.tpBound, hpTable, tpTable)

      val (hpErrs, _) = swappedHPBounds
        .map(HPBound.verifyMeetBound(_, callerHPBound))
        .partitionMap(identity)

      val (tpErrs, _) = swappedTPBounds
        .map(TPBound.verifyMeetBound(_, callerHPBound, callerTPBound))
        .partitionMap(identity)

      if(hpErrs.isEmpty && tpErrs.isEmpty) Right(())
      else Left(Error.MultipleErrors(hpErrs ++ tpErrs: _*))
    }

    val (errs, _) = results.partitionMap(identity)
    if(errs.isEmpty) Right(())
    else Left(Error.MultipleErrors(errs: _*))
     */
  }
}

class HPBound(
  val target: HPExpr,
  val bound: HPRange
) extends Bound {
  def composeBound(composed: HPRange): Either[Error, HPRange] = (this.bound, composed) match {
    case (HPRange.Eq(HPRange.ExprEqual(origin)), HPRange.Eq(HPRange.ExprEqual(composed))) =>
      if (origin.isSameExpr(composed)) Right(this.bound)
      else Left(???)
    case (HPRange.Eq(HPRange.ConstantEqual(v0)), HPRange.Eq(HPRange.ConstantEqual(v1))) =>
      if (v0 == v1) Right(this.bound)
      else Left(???)
    case (HPRange.Eq(_), HPRange.Eq(_)) => Left(???)
    case (_: HPRange.Range, _: HPRange.Eq) => Left(???)
    case (_: HPRange.Eq, _: HPRange.Range) => Left(???)
    case (HPRange.Range(thisExprRange, thisConstRange), HPRange.Range(thatExprRange, thatConstRange)) =>
      def compose(origin: Vector[HPExpr], composed: Vector[HPExpr]): Vector[HPExpr] =
        composed.foldLeft(origin) {
          case (acc, expr) => acc.find(_.isSameExpr(expr)) match {
            case None => acc :+ expr
            case Some(_) => acc
          }
        }

      def select(origin: IInt, composed: IInt)(cond: (IInt, IInt) => Boolean): IInt =
        if (cond(origin, composed)) composed
        else origin

      val newMax = compose(thisExprRange.max, thatExprRange.max)
      val newMin = compose(thisExprRange.min, thatExprRange.min)
      val newNEs = compose(thisExprRange.ne, thatExprRange.ne)
      val newCMax = select(thisConstRange.max, thatConstRange.max)(_ > _)
      val newCMin = select(thisConstRange.min, thatConstRange.min)(_ < _)
      val newCNE = thisConstRange.ne ++ thatConstRange.ne

      val newExprRange = HPRange.ExprRange(newMax, newMin, newNEs)
      val newConstRange = HPRange.ConstantRange(newCMax, newCMin, newCNE)

      Right(HPRange.Range(newExprRange, newConstRange))
  }

  override def equals(obj: Any): Boolean = obj match {
    case that: HPBound =>
      this.target.isSameExpr(that.target) &&
      this.bound == that.bound
    case _ => false
  }
}

object HPBound {
  def apply(bound: HPBoundTree): HPBound = {
    val (constMins, remains0) = bound.bounds.collectPartition {
      case RangeExpr.Min(IntLiteral(value)) => IInt(value)
    }

    val (constMaxs, remains1) = remains0.collectPartition {
      case RangeExpr.Max(IntLiteral(value)) => IInt(value)
    }

    val (constNEs, remains2) = remains1.collectPartition {
      case RangeExpr.NE(IntLiteral(value)) => value
    }

    val (constEQs, remains3) = remains2.collectPartition {
      case RangeExpr.EQ(IntLiteral(value)) => value
    }

    val (exprMins, remains4) = remains3.collectPartition {
      case RangeExpr.Min(expr) => expr
    }

    val (exprMaxs, remains5) = remains4.collectPartition {
      case RangeExpr.Max(expr) => expr
    }

    val (exprNEs, remains6) = remains5.collectPartition {
      case RangeExpr.NE(expr) => expr
    }

    val exprEQs = remains6.map { case RangeExpr.EQ(expr) => expr }

    if (constEQs.nonEmpty) HPBound(bound.target, HPRange.Eq(HPRange.ConstantEqual(constEQs.head)))
    else if (exprEQs.nonEmpty) HPBound(bound.target, HPRange.Eq(HPRange.ExprEqual(exprEQs.head)))
    else {
      val constMin = constMins.foldLeft(IInt.nInf) { case (acc, min) => if (acc < min) min else acc }
      val constMax = constMaxs.foldLeft(IInt.pInf) { case (acc, max) => if (acc > max) max else acc }
      val constNESet = constNEs.toSet
      val cRange = HPRange.ConstantRange(constMax, constMin, constNESet)
      val eRange = HPRange.ExprRange(exprMaxs, exprMins, exprNEs)

      HPBound(bound.target, HPRange.Range(eRange, cRange))
    }
  }

  def apply(target: HPExpr, range: HPRange): HPBound =
    new HPBound(target, range)

  def simplify(replacedHPBound: Vector[HPBound]): Either[Error, Vector[HPBound]] = {
    def compose: Either[Error, Vector[HPBound]] = {
      def execCompose(
        targets: Vector[HPBound],
        hpBound: HPBound,
        remains: Vector[HPBound]
      ): Either[Error, Vector[HPBound]] =
        targets match {
          case Vector() => Right(remains :+ hpBound)
          case Vector(bound) =>
            hpBound.composeBound(bound.bound) match {
              case Left(err) => Left(err)
              case Right(range) => Right(remains :+ HPBound(hpBound.target, range))
            }
          case _ => throw new ImplementationErrorException("this pattern should not reached")
        }

      replacedHPBound.foldLeft[Either[Error, Vector[HPBound]]](Right(Vector.empty[HPBound])) {
        case (Right(acc), hpBound) =>
          val (sameTarget, remains) = acc.partition(_.target.isSameExpr(hpBound.target))
          execCompose(sameTarget, hpBound, remains)
        case (Left(err), _) => Left(err)
      }
    }

    @tailrec
    def delegateConstRange(delegated: Vector[HPBound]): Either[Error, Vector[HPBound]] = {
      var isDelegated = false

      val newBounds = delegated.map { hpBound =>
        hpBound.bound match {
          case HPRange.Eq(HPRange.ConstantEqual(_)) => hpBound
          case HPRange.Eq(HPRange.ExprEqual(expr)) => delegated.find(_.target.isSameExpr(expr)) match {
            case None => hpBound
            case Some(lookupBound) => lookupBound.bound match {
              case const@HPRange.Eq(_: HPRange.ConstantEqual) => HPBound(hpBound.target, const)
              case _ => hpBound
            }
          }
          case HPRange.Range(eRange, cRange) =>
            def restrictConstRange(eRange: Vector[HPExpr], init: IInt)(g: HPRange.ConstantRange => IInt)(f: (IInt, IInt) => IInt): IInt =
              eRange.foldLeft(init) {
                case (acc, edge) => delegated.find(_.target.isSameExpr(edge)) match {
                  case None => acc
                  case Some(lookupBound) => lookupBound.bound match {
                    case HPRange.Eq(HPRange.ConstantEqual(v)) => f(IInt(v), acc)
                    case HPRange.Eq(HPRange.ExprEqual(_)) => acc
                    case HPRange.Range(_, cRange) => f(g(cRange), acc)
                  }
                }
              }

            val newMax = restrictConstRange(eRange.max, cRange.max)(_.max) { (max, acc) =>
              if (max < acc) max
              else acc
            }

            val newMin = restrictConstRange(eRange.min, cRange.min)(_.min) { (min, acc) =>
              if (min > acc) min
              else acc
            }

            val newNEs = eRange.ne.foldLeft(cRange.ne) {
              case (acc, ne) => delegated.find(_.target.isSameExpr(ne)) match {
                case None => acc
                case Some(lookupBound) => lookupBound.bound match {
                  case HPRange.Eq(HPRange.ConstantEqual(v)) => acc + v
                  case _ => acc
                }
              }
            }

            val newRange = HPRange.ConstantRange(newMax, newMin, newNEs)
            if (newRange == cRange) hpBound
            else {
              isDelegated = true
              HPBound(hpBound.target, HPRange.Range(eRange, newRange))
            }
        }
      }

      if (!isDelegated) Right(newBounds)
      else delegateConstRange(newBounds)
    }

    for {
      composed <- compose
      delegated <- delegateConstRange(composed)
    } yield delegated
  }

  def verifyForm(bound: HPBoundTree)(implicit ctx: Context.NodeContext, global: GlobalData): Either[Error, Unit] = {
    def verifyExpr(expr: HPExpr): Either[Error, HPExpr] = expr match {
      case lit: StringLiteral => Right(lit.setTpe(Type.strTpe))
      case lit: IntLiteral => Right(lit.setTpe(Type.numTpe))
      case ident: Ident => ctx
        .lookup[Symbol.HardwareParamSymbol](ident.name)
        .toEither
        .map(symbol => ident.setSymbol(symbol).setTpe(symbol.tpe))
      case HPBinOp(op, left, right) =>
        val terms = for {
          typedLeft  <- verifyExpr(left)
          typedRight <- verifyExpr(right)
        } yield (typedLeft, typedRight)

        terms.flatMap {
          case (left, right) => (left.tpe, right.tpe) match {
            case (Type.ErrorType, _) => Left(Error.DummyError)
            case (_, Type.ErrorType) => Left(Error.DummyError)
            case (leftTpe: Type.RefType, rightTpe: Type.RefType) =>
              lazy val typedBinOp = HPBinOp(op, left, right).setTpe(Type.numTpe).setID(expr.id)
              lazy val leftTypeMissMatch = Error.TypeMismatch(Type.numTpe, leftTpe)
              lazy val rightTypeMissMatch = Error.TypeMismatch(Type.numTpe, rightTpe)

              if(leftTpe =:= Type.numTpe && rightTpe =:= Type.numTpe) Right(typedBinOp)
              else if (leftTpe =!= Type.numTpe && rightTpe =!= Type.numTpe)
                Left(Error.MultipleErrors(leftTypeMissMatch, rightTypeMissMatch))
              else if(leftTpe =!= Type.numTpe) Left(leftTypeMissMatch)
              else Left(rightTypeMissMatch)
          }
        }
    }

    def verifyTarget(expr: HPExpr): Either[Error, Unit] = {
      val result = expr match {
        case lit: StringLiteral => Left(Error.LiteralOnTarget(lit))
        case lit: IntLiteral => Left(Error.LiteralOnTarget(lit))
        case expr => verifyExpr(expr)
      }

      result.map(_ => ())
    }

    def verifyBound(bound: Vector[RangeExpr]): Either[Error, Unit] = {
      case class Range(max: Option[Int], min: Option[Int], eq: Option[Int])

      def verifyRanges(remain: Vector[RangeExpr], assignedRange: Range): Either[Error, Unit] = {
        def verify(expr: HPExpr)(rootPattern: PartialFunction[HPExpr, Either[Error, Range]]): Either[Error, Range] = {
          rootPattern.applyOrElse(expr, (expr: HPExpr) => verifyExpr(expr).map(_ => assignedRange))
          /*
          rootPattern.unapply(expr) match {
            case Some(ret) => ret
            case None => verifyExpr(expr).map(_ => assignedRange)
          }
          */
        }

        if (remain.isEmpty) Right(())
        else {
          val result = remain.head match {
            case RangeExpr.EQ(expr) => verify(expr) {
              case IntLiteral(value) => assignedRange.eq match {
                case None => Right(assignedRange.copy(eq = Some(value)))
                case Some(eq) => Left(Error.RangeAlreadyAssigned[RangeExpr.EQ](eq))
              }
            }
            case RangeExpr.NE(expr) => verify(expr) {
              case _: IntLiteral => Right(assignedRange)
            }
            case RangeExpr.Max(expr) => verify(expr) {
              case IntLiteral(value) => assignedRange.max match {
                case None => Right(assignedRange.copy(max = Some(value)))
                case Some(max) => Left(Error.RangeAlreadyAssigned[RangeExpr.Max](max))
              }
            }
            case RangeExpr.Min(expr) => verify(expr) {
              case IntLiteral(value) => assignedRange.min match {
                case None => Right(assignedRange.copy(min = Some(value)))
                case Some(min) => Left(Error.RangeAlreadyAssigned[RangeExpr.Min](min))
              }
            }
          }

          result.flatMap(verifyRanges(remain.tail, _))
        }
      }

      val (eqs, others) = bound.partition(_.isInstanceOf[RangeExpr.EQ])

      if (eqs.nonEmpty && others.nonEmpty) Left(Error.EqAndOthersInSameBound(eqs, others))
      else verifyRanges(bound, Range(None, None, None))
    }

    for {
      _ <- verifyTarget(bound.target)
      _ <- verifyBound(bound.bounds)
    } yield ()
  }

  def verifyAllForms(bounds: Vector[HPBoundTree])(implicit ctx: Context.NodeContext, global: GlobalData): Either[Error, Unit] = {
    val (errs, _) = bounds.map(HPBound.verifyForm).partitionMap(identity)

    if (errs.isEmpty) Right(())
    else Left(Error.MultipleErrors(errs: _*))
  }

  def swapBounds(
    swapped: Vector[HPBound],
    table: Map[Symbol.HardwareParamSymbol, HPExpr]
  ): Vector[HPBound] = {
    def swap(expr: HPExpr): HPExpr = expr.swap(table)
    def sort(expr: HPExpr): HPExpr = expr.sort

    def swapBound(hpBound: HPBound): HPBound = {
      val target = hpBound.target.swap(table).sort
      val bound = hpBound.bound match {
        case HPRange.Eq(HPRange.ExprEqual(expr)) =>
          (HPRange.Eq compose HPRange.ExprEqual compose sort compose swap)(expr)
        case eqn @ HPRange.Eq(_: HPRange.ConstantEqual) => eqn
        case HPRange.Range(eRange, cRange) =>
          val f = sort _ compose swap
          val max = eRange.max.map(f)
          val min = eRange.min.map(f)
          val ne = eRange.ne.map(f)

          HPRange.Range(HPRange.ExprRange(max, min, ne), cRange)
      }

      HPBound(target, bound)
    }

    swapped.map(swapBound)
  }

  def verifyMeetBound(swapped: HPBound, callerHPBounds: Vector[HPBound]): Either[Error, Unit] = {
    def valueMeetBound(value: Int): Either[Error, Unit] = {
      def error: Left[Error, Unit] = Left(Error.ValueNotMeetHPBound(value, swapped))

      swapped.bound match {
        case HPRange.Eq(HPRange.ExprEqual(_)) => error
        case HPRange.Eq(HPRange.ConstantEqual(that)) =>
          if (value == that) Right(())
          else error
        case HPRange.Range(eRange, cRange) =>
          val v = IInt(value)

          def rangeDefinitely(ranges: Vector[HPExpr])(f: (IInt, IInt) => Boolean): Boolean =
            ranges.forall { expr =>
              callerHPBounds.find(_.target.isSameExpr(expr)) match {
                case None => false
                case Some(bound) => bound.bound match {
                  case HPRange.Eq(_: HPRange.ExprEqual) => false
                  case HPRange.Eq(HPRange.ConstantEqual(that)) => f(IInt(that), v)
                  case HPRange.Range(_, cRange) => f(cRange.min, v)
                }
              }
            }

          lazy val validMax = rangeDefinitely(eRange.max)(_ >= _)
          lazy val validMin = rangeDefinitely(eRange.min)(_ >= _)
          lazy val validNE = eRange.ne.forall {
            expr =>
              callerHPBounds.find(_.target.isSameExpr(expr)) match {
                case None => false
                case Some(bound) => bound.bound match {
                  case HPRange.Eq(_: HPRange.ExprEqual) => false
                  case HPRange.Eq(HPRange.ConstantEqual(that)) => that != value
                  case HPRange.Range(_, cRange) => cRange.min > v || cRange.max < v
                }
              }
          }

          val isValid =
            cRange.min <= v &&
              cRange.max >= v &&
              !cRange.ne.contains(value) &&
              validMax &&
              validMin &&
              validNE

          if (isValid) Right(())
          else error
      }
    }

    def exprMeetBound(expr: HPExpr): Either[Error, Unit] = {
      def buildError(caller: HPBound): Left[Error, Unit] =
        Left(Error.NotMeetHPBound(swapped, Some(caller)))

      val derivedRange = callerHPBounds
        .find(_.target.isSameExpr(expr))
        .map(Right.apply)
        .getOrElse(deriveRange(expr, callerHPBounds).map(HPBound(expr, _)))

      derivedRange match {
        case Left(err) => Left(err)
        case Right(callerBound) => callerBound.bound match {
          case HPRange.Eq(HPRange.ExprEqual(callerExpr)) => swapped.bound match {
            case HPRange.Eq(HPRange.ExprEqual(replacedExpr)) =>
              if (replacedExpr.isSameExpr(callerExpr)) Right(())
              else buildError(callerBound)
            case _ => buildError(callerBound)
          }
          case HPRange.Eq(HPRange.ConstantEqual(callerValue)) => valueMeetBound(callerValue)
          case HPRange.Range(callerExprRange, callerConstRange) => swapped.bound match {
            case HPRange.Eq(_) => buildError(callerBound)
            case HPRange.Range(replacedExprRange, replacedConstRange) =>
              def verifyExprRange(replacedRange: Vector[HPExpr], callerRange: Vector[HPExpr]): Boolean =
                replacedRange.forall {
                  rRangeExpr =>
                    callerRange.exists {
                      cRangeExpr => rRangeExpr.isSameExpr(cRangeExpr)
                    }
                }

              lazy val validMax = verifyExprRange(replacedExprRange.max, callerExprRange.max)
              lazy val validMin = verifyExprRange(replacedExprRange.min, callerExprRange.min)
              lazy val validNEs = verifyExprRange(replacedExprRange.ne, callerExprRange.ne)

              lazy val validCMax = callerConstRange.max <= replacedConstRange.max
              lazy val validCMin = callerConstRange.min >= replacedConstRange.min
              lazy val validCNEs = replacedConstRange.ne.forall(callerConstRange.ne.contains)

              val isValid = validCMax && validCMin && validCNEs && validMax && validMin && validNEs

              if (isValid) Right(())
              else buildError(callerBound)
          }
        }
      }
    }

    def deriveRange(expr: HPExpr, callerHPBounds: Vector[HPBound]): Either[Error, HPRange] = {
      def splitConstant(expr: HPExpr): (HPExpr, Option[(Operation, IntLiteral)]) =
        expr match {
          case ident: Ident => (ident, None)
          case literal: IntLiteral => (literal, None)
          case HPBinOp(op, left, right: IntLiteral) => (left, Some(op, right))
          case binop: HPBinOp => (binop, None)
        }

      def buildFromConstEq(equal: HPRange.ConstantEqual)(f: IInt => IInt): Either[Error, HPRange] = {
        f(IInt(equal.num)) match {
          case IInt.Integer(value) => Right(HPRange.Eq(HPRange.ConstantEqual(value)))
          case _ => Left(???)
        }
      }

      def buildFronConstRange(range: HPRange.ConstantRange)(f: IInt => IInt): Either[Error, HPRange] = {
        val range0 = f(range.max)
        val range1 = f(range.min)

        if(range0 == range1) {
          range0 match {
            case IInt.Integer(value) =>
              val constEq = HPRange.ConstantEqual(value)
              Right(HPRange.Eq(constEq))
            case _ => Left(???) // Constant Equal but Positive Inf or Negative Inf is error
          }
        } else {
          val (max, min) =
            if(range0 > range1) (range0, range1)
            else (range1, range0)

          val ne = range.ne
            .map(value => f(IInt(value)))
            .collect{ case IInt.Integer(value) => value }

          val exprRange = HPRange.ExprRange(Vector.empty, Vector.empty, Vector.empty)
          val constRange = HPRange.ConstantRange(max, min, ne)
          Right(HPRange.Range(exprRange, constRange))
        }
      }

      def constructRange(expr: HPExpr): Either[Error, HPRange] = {
        def getOperand(expr: HPRange): Vector[IInt] = expr match {
          case HPRange.Range(_, HPRange.ConstantRange(max, min, _)) => Vector(max, min)
          case HPRange.Eq(HPRange.ConstantEqual(value)) => Vector(IInt(value))
        }

        def selectEdge(values: Vector[IInt])(f: (IInt, IInt) => Boolean): IInt = {
          values.tail.foldLeft(values.head) {
            case (remain, edge) =>
              if(f(edge, remain)) edge
              else remain
          }
        }

        def calcRange(left: HPRange, right: HPRange, op: Operation): Either[Error, HPRange] = {
          val lefts = getOperand(left)
          val rights = getOperand(right)

          val operands = for {
            l <- lefts
            r <- rights
          } yield (l, r)

          val f: (IInt, IInt) => IInt = op match {
            case Operation.Add => _ + _
            case Operation.Sub => _ - _
            case Operation.Mul => _ * _
            case Operation.Div => _ / _
          }

          val values = operands.map{ case (l, r) => f(l, r) }
          val max = selectEdge(values)(_ > _)
          val min = selectEdge(values)(_ < _)

          if(max != min) Right(HPRange.Range(HPRange.ExprRange.empty, HPRange.ConstantRange(max, min, Set.empty)))
          else max match {
            case IInt.Integer(value) => Right(HPRange.Eq(HPRange.ConstantEqual(value)))
            case _ => Left(???)
          }
        }

        def loop(expr: HPExpr): Either[Error, HPRange] = {
          expr match {
            case IntLiteral(value) => Right(HPRange.Eq(HPRange.ConstantEqual(value)))
            case ident: Ident =>
              val range = callerHPBounds
                .find(_.target.isSameExpr(ident))
                .map(_.bound)
                .filterNot(_.isInstanceOf[HPRange.ExprEqual])
                .getOrElse(HPRange.Range.empty)

              Right(range)
            case HPBinOp(op, left, right) =>
              for {
                l <- loop(left)
                r <- loop(right)
                range <- calcRange(l, r, op)
              } yield range
          }
        }

        loop(expr)
      }

      val (remain, constant) = splitConstant(expr)
      val range = callerHPBounds
        .find(_.target.isSameExpr(remain))
        .map(_.bound)
        .map(Right.apply)
        .getOrElse(constructRange(remain))

      range match {
        case Left(err) => Left(err)
        case Right(range) => constant match {
          case None => Right(range)
          case Some((op, IntLiteral(value))) =>
            val f: IInt => IInt = op match {
              case Operation.Add => _ + IInt(value)
              case Operation.Sub => _ - IInt(value)
              case Operation.Mul => _ * IInt(value)
              case Operation.Div => _ / IInt(value)
            }

            range match {
              case HPRange.Eq(eq: HPRange.ConstantEqual) => buildFromConstEq(eq)(f)
              case HPRange.Eq(_) => Right(HPRange.Range.empty)
              case HPRange.Range(_, consts) => buildFronConstRange(consts)(f)
            }
        }
      }
    }

    swapped.target match {
      case IntLiteral(value) => valueMeetBound(value)
      case expr: HPExpr => exprMeetBound(expr)
    }
  }
}

trait HPRange {
  def isOverlapped(that: HPRange): Boolean
  def isOverlapped(value: Int): Boolean
  def isSubsetOf(that: HPRange): Boolean
  def isSubsetOf(value: Int): Boolean
}

object HPRange {
  case class ExprRange(max: Vector[HPExpr], min: Vector[HPExpr], ne: Vector[HPExpr]) {
    override def equals(obj: Any): Boolean = obj match {
      case that: HPRange.ExprRange =>
        @tailrec def forall(thisExpr: Vector[HPExpr], thatExpr: Vector[HPExpr]): Boolean =
          thatExpr.headOption match {
            case None => true
            case Some(head) => thisExpr.findRemain(_.isSameExpr(head)) match {
              case (None, _) => false
              case (Some(_), remains) => forall(remains, thatExpr.tail)
            }
          }

        this.max.length == that.max.length &&
        this.min.length == that.min.length &&
        this.ne.length == that.ne.length &&
        forall(this.max, that.max) &&
        forall(this.min, that.min) &&
        forall(this.ne, that.ne)
      case _ => false
    }
  }

  object ExprRange {
    def empty: HPRange.ExprRange = HPRange.ExprRange(Vector.empty, Vector.empty, Vector.empty)
  }

  case class ConstantRange(max: IInt, min: IInt, ne: Set[Int]) {
    override def equals(obj: Any): Boolean = obj match {
      case that: HPRange.ConstantRange =>
        this.max == that.max &&
        this.min == that.min &&
        this.ne == that.ne
      case _ => false
    }
  }

  case class Range(eRange: ExprRange, cRange: ConstantRange) extends HPRange {
    override def isOverlapped(that: HPRange): Boolean = that match {
      case that: HPRange.Range =>
        this.cRange.min <= that.cRange.max &&
        that.cRange.min <= this.cRange.max
      case HPRange.Eq(ConstantEqual(value)) =>
        val v = IInt(value)
        v <= this.cRange.max && v >= this.cRange.min
      case HPRange.Eq(_: ExprEqual) => true
    }

    override def isOverlapped(that: Int): Boolean = {
      val value = IInt(that)

      this.cRange.max >= value && this.cRange.min <= value
    }

    override def isSubsetOf(that: HPRange): Boolean = that match {
      case _: HPRange.Eq => false
      case that: HPRange.Range =>
        this.cRange.max <= that.cRange.max &&
          this.cRange.min >= that.cRange.min
    }

    override def isSubsetOf(value: Int): Boolean = false

    override def equals(obj: Any): Boolean = obj match {
      case that: HPRange.Range =>
        this.eRange == that.eRange &&
        this.cRange == that.cRange
      case _ => false
    }
  }

  object Range {
    def empty: HPRange.Range = Range(
      ExprRange(Vector.empty, Vector.empty, Vector.empty),
      ConstantRange(IInt.PInf, IInt.NInf, Set.empty)
    )
  }

  trait Equal
  case class ExprEqual(expr: HPExpr) extends Equal {
    override def equals(obj: Any): Boolean = obj match {
      case that: HPRange.ExprEqual => this.expr.isSameExpr(that.expr)
      case _ => false
    }
  }
  case class ConstantEqual(num: Int) extends Equal {
    override def equals(obj: Any): Boolean = obj match {
      case that: HPRange.ConstantEqual => this.num == that.num
      case _ => false
    }
  }

  case class Eq(eqn: Equal) extends HPRange {
    override def isOverlapped(that: HPRange): Boolean = {
      that match {
        case that: HPRange.Range => eqn match {
          case _: ExprEqual => true
          case ConstantEqual(value) => that.isOverlapped(value)
        }
        case HPRange.Eq(ConstantEqual(v0)) => eqn match {
          case _: ExprEqual => true
          case ConstantEqual(v1) => v0 == v1
        }
        case HPRange.Eq(_: ExprEqual) => true
      }
    }

    override def isOverlapped(value: Int): Boolean = this.eqn match {
      case _: ExprEqual => true
      case ConstantEqual(v) => v == value
    }

    override def isSubsetOf(that: HPRange): Boolean =
      that match {
        case HPRange.Eq(ConstantEqual(thatValue)) => this.eqn match {
          case ConstantEqual(thisValue) => thisValue == thatValue
          case ExprEqual(_) => false
        }
        case HPRange.Eq(ExprEqual(_)) => this.eqn match {
          case ConstantEqual(_) => false
          case ExprEqual(_) => true
        }
        case range: HPRange.Range => this.eqn match {
          case ConstantEqual(thisValue) =>
            val value = IInt(thisValue)
            range.cRange.max >= value &&
              range.cRange.min <= value &&
              !range.cRange.ne.contains(thisValue)
          case ExprEqual(_) =>
            range.cRange.max.isPInf &&
              range.cRange.min.isNInf
        }
      }

    override def isSubsetOf(value: Int): Boolean = this.eqn match {
      case ConstantEqual(thisValue) => thisValue == value
      case ExprEqual(_) => false
    }

    override def equals(obj: Any): Boolean = obj match {
      case that: HPRange.Eq => this.eqn == that.eqn
      case _ => false
    }
  }

}

