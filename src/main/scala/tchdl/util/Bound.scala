package tchdl.util

import tchdl.ast._
import tchdl.util.TchdlException.ImplementationErrorException

import scala.annotation.tailrec

trait Bound

class TPBound(
  val target: Type.RefType,
  val bounds: Vector[Type.RefType]
) extends Bound

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
      lazy val swappedHP = tpe.hardwareParam.view.map(swapHP).map(_.sort).to(Vector)
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
  ): Either[Error, Unit] =
    swapped.target.origin match {
      case _: Symbol.EntityTypeSymbol => verifyEntityTarget(swapped, callerHPBound, callerTPBound)
      case _: Symbol.TypeParamSymbol => verifyTypeParamTarget(swapped, callerHPBound, callerTPBound)
    }

  def verifyEntityTarget(
    tpBound: TPBound,
    callerHPBound: Vector[HPBound],
    callerTPBound: Vector[TPBound]
  ): Either[Error, Unit] = {
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

    val results = tpBound.bounds.map { bound =>
      val impls = bound.origin.asInterfaceSymbol.impls
      val isValid = impls.exists(impl => verify(impl, bound))

      if(isValid) Right(())
      else Left(Error.NotMeetPartialTPBound(tpBound.target, bound))
    }

    val (errs, _) = results.partitionMap(identity)

    if(errs.isEmpty) Right(())
    else Left(Error.MultipleErrors(errs: _*))
  }

  def verifyTypeParamTarget(
    tpBound: TPBound,
    callerHPBound: Vector[HPBound],
    callerTPBound: Vector[TPBound]
  ): Either[Error, Unit] = {
    val results = tpBound.bounds.map { bound =>
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

  def verifyForm(bound: HPBoundTree)(implicit ctx: Context.NodeContext): Either[Error, Unit] = {
    def verifyTarget(expr: HPExpr): Either[Error, Unit] = {
      def loop(expr: HPExpr, isRoot: Boolean): Either[Error, Unit] = {
        expr match {
          case HPBinOp(_, left, right) =>
            for {
              _ <- loop(left, isRoot = false)
              _ <- loop(right, isRoot = false)
            } yield ()
          case Ident(name) =>
            ctx.lookupDirectLocal[Symbol.HardwareParamSymbol](name) match {
              case LookupResult.LookupFailure(err) => Left(err)
              case LookupResult.LookupSuccess(_) => Right(())
            }
          case _ /*Literal*/ if isRoot => Left(???)
          case _ => Right(())
        }
      }

      loop(expr, isRoot = true)
    }

    def verifyBound(bound: Vector[RangeExpr]): Either[Error, Unit] = {
      case class Range(max: Option[Int], min: Option[Int], eq: Option[Int])

      def verifyRanges(remain: Vector[RangeExpr], assignedRange: Range): Either[Error, Unit] = {
        def collectIdent(expr: HPExpr): Vector[Ident] = expr match {
          case HPBinOp(_, left, right) => collectIdent(left) ++ collectIdent(right)
          case ident: Ident => Vector(ident)
          case _ => Vector.empty
        }

        def verifyAllIdents(idents: Vector[Ident]): Either[Error, Range] = {
          val (errs, _) = idents.view
            .map(_.name)
            .map(ctx.lookupDirectLocal[Symbol.HardwareParamSymbol])
            .map(_.toEither)
            .to(Vector)
            .partitionMap(identity)

          if (errs.isEmpty) Right(assignedRange)
          else Left(Error.MultipleErrors(errs: _*))
        }

        def verifyExpr(expr: HPExpr)(intLitCase: PartialFunction[HPExpr, Either[Error, Range]]): Either[Error, Range] = {
          intLitCase.unapply(expr) match {
            case Some(ret) => ret
            case None => expr match {
              case _: StringLiteral => Left(???)
              case binop: HPBinOp => (collectIdent _ andThen verifyAllIdents)(binop)
              case ident: Ident => verifyAllIdents(Vector(ident))
            }
          }
        }

        if (remain.isEmpty) Right(())
        else {
          val result = remain.head match {
            case RangeExpr.EQ(expr) => verifyExpr(expr) {
              case IntLiteral(value) => assignedRange.eq match {
                case None => Right(assignedRange.copy(eq = Some(value)))
                case Some(_) => Left(???)
              }
            }
            case RangeExpr.NE(expr) => verifyExpr(expr) {
              case _: IntLiteral => Right(assignedRange)
            }
            case RangeExpr.Max(expr) => verifyExpr(expr) {
              case IntLiteral(value) => assignedRange.max match {
                case None => Right(assignedRange.copy(max = Some(value)))
                case Some(_) => Left(???)
              }
            }
            case RangeExpr.Min(expr) => verifyExpr(expr) {
              case IntLiteral(value) => assignedRange.min match {
                case None => Right(assignedRange.copy(min = Some(value)))
                case Some(_) => Left(???)
              }
            }
          }

          result.flatMap(verifyRanges(remain.tail, _))
        }
      }

      val (eqs, others) = bound.partition {
        case _: RangeExpr.EQ => true
        case _ => false
      }

      if (eqs.nonEmpty && others.nonEmpty) Left(???)
      else verifyRanges(bound, Range(None, None, None))
    }

    for {
      _ <- verifyTarget(bound.target)
      _ <- verifyBound(bound.bounds)
    } yield ()
  }

  def verifyAll(bounds: Vector[HPBoundTree])(implicit ctx: Context.NodeContext): Either[Error, Unit] = {
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

      callerHPBounds.find(_.target.isSameExpr(expr)) match {
        case None => Left(Error.NotMeetHPBound(swapped, None))
        case Some(callerBound) => callerBound.bound match {
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
  case class ExprRange(max: Vector[HPExpr], min: Vector[HPExpr], ne: Vector[HPExpr])
  case class ConstantRange(max: IInt, min: IInt, ne: Set[Int])

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
  }

  object Range {
    def empty: Range = Range(
      ExprRange(Vector.empty, Vector.empty, Vector.empty),
      ConstantRange(IInt.PInf, IInt.NInf, Set.empty)
    )
  }

  trait Equal
  case class ExprEqual(expr: HPExpr) extends Equal
  case class ConstantEqual(num: Int) extends Equal

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
  }

}

