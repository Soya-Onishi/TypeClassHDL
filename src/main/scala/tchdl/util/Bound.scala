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
    position: Position
  )(implicit global: GlobalData): Either[Error, Unit] = {
    val (hpErrs, _) = hpBounds
      .map(HPBound.verifyMeetBound(_, callerHPBound))
      .partitionMap(identity)

    val (tpErrs, _) = tpBounds
      .map(TPBound.verifyMeetBound(_, callerHPBound, callerTPBound, position))
      .partitionMap(identity)

    val errs = hpErrs ++ tpErrs
    if (errs.isEmpty) Right(())
    else Left(Error.MultipleErrors(errs: _*))
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
      case HPUnaryOp(ident) => swapHP(ident)
      case bin @ HPBinOp(left, right) => HPBinOp(swapHP(left), swapHP(right), bin.position)
      case lit => lit
    }

    def swapTP(tpe: Type.RefType): Type.RefType = {
      lazy val swappedTP = tpe.typeParam.map(swapTP)
      lazy val swappedHP = tpe.hardwareParam.view.map(swapHP).map(_.sort).toVector
      tpe.origin match {
        case _: Symbol.EntityTypeSymbol =>
          Type.RefType(tpe.origin, swappedHP, swappedTP, tpe.isPointer)
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
    callerTPBound: Vector[TPBound],
    position: Position
  )(implicit global: GlobalData): Either[Error, Unit] =
    swapped.target.origin match {
      case _: Symbol.EntityTypeSymbol => verifyEntityTarget(swapped, callerHPBound, callerTPBound, position)
      case _: Symbol.TypeParamSymbol => verifyTypeParamTarget(swapped, callerTPBound, position)
    }

  private def verifyEntityTarget(
    tpBound: TPBound,
    callerHPBound: Vector[HPBound],
    callerTPBound: Vector[TPBound],
    position: Position
  )(implicit global: GlobalData): Either[Error, Unit] = {
    lazy val hwSymbol = global.builtin.interfaces.lookup("HW")
    lazy val modSymbol = global.builtin.interfaces.lookup("Module")

    def verify(impl: ImplementInterfaceContainer, bound: Type.RefType, position: Position): Boolean = {
      val initHPTable = impl.hardwareParam.map(_ -> Option.empty[HPExpr]).toMap
      val initTPTable = impl.typeParam.map(_ -> Option.empty[Type.RefType]).toMap
      val targets = Vector(impl.targetType, impl.targetInterface)
      val referer = Vector(tpBound.target, bound)

      val result = for {
        _ <- Type.RefType.verifySuperSets(referer, targets, Vector.fill(referer.length)(position))
        hpTable <- Type.RefType.assignHPTable(initHPTable, referer, targets, position)
        tpTable <- Type.RefType.assignTPTable(initTPTable, referer, targets, position)
        swappedHPBounds = HPBound.swapBounds(impl.symbol.hpBound, hpTable)
        swappedTPBounds = TPBound.swapBounds(impl.symbol.tpBound, hpTable, tpTable)
        _ <- {
          val (hpErrs, _) = swappedHPBounds
            .map(HPBound.verifyMeetBound(_, callerHPBound))
            .partitionMap(identity)

          val (tpErrs, _) = swappedTPBounds
            .map(TPBound.verifyMeetBound(_, callerHPBound, callerTPBound, position))
            .partitionMap(identity)

          val errs = hpErrs ++ tpErrs
          if (errs.isEmpty) Right(())
          else Left(Error.MultipleErrors(errs: _*))
        }
      } yield ()

      result.isRight
    }

    def isModuleType(tpe: Type.RefType): Boolean = tpe.origin match {
      case _: Symbol.ModuleSymbol => true
      case _: Symbol.InterfaceSymbol => false
      case tp: Symbol.TypeParamSymbol => callerTPBound.find(_.target.origin == tp) match {
        case None => false
        case Some(tpBound) =>
          val moduleInterface = Type.RefType(global.builtin.interfaces.lookup("Module"), isPointer = Some(false))
          tpBound.bounds.exists(_ =:= moduleInterface)
      }
    }

    val results = tpBound.bounds.map { bound =>
      bound.origin match {
        case hw if hw == hwSymbol =>
          if (tpBound.target.isHardwareType(callerTPBound)(position, global)) Right(())
          else Left(Error.NotMeetPartialTPBound(tpBound.target, bound, position))
        case mod if mod == modSymbol =>
          if (isModuleType(tpBound.target)) Right(())
          else Left(Error.NotMeetPartialTPBound(tpBound.target, bound, position))
        case interface: Symbol.InterfaceSymbol =>
          val impls = interface.impls
          val isValid = impls.exists(impl => verify(impl, bound, position))

          if (isValid) Right(())
          else Left(Error.NotMeetPartialTPBound(tpBound.target, bound, position))
      }
    }

    val (errs, _) = results.partitionMap(identity)

    if (errs.isEmpty) Right(())
    else Left(Error.MultipleErrors(errs: _*))
  }

  private def verifyTypeParamTarget(
    swappedTPBound: TPBound,
    callerTPBound: Vector[TPBound],
    position: Position
  ): Either[Error, Unit] = {
    callerTPBound.find(_.target.origin == swappedTPBound.target.origin) match {
      case Some(bound) =>
        val results = swappedTPBound.bounds.map {
          calledBound =>
            if (bound.bounds.contains(calledBound)) Right(())
            else Left(Error.NotMeetPartialTPBound(swappedTPBound.target, calledBound, position))
        }

        val (errs, _) = results.partitionMap(identity)
        if (errs.isEmpty) Right(())
        else Left(Error.MultipleErrors(errs: _*))
      case None =>
        val isValid = swappedTPBound.bounds.isEmpty
        lazy val errs = swappedTPBound
          .bounds
          .map(Error.NotMeetPartialTPBound(swappedTPBound.target, _, position))

        if (isValid) Right(())
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

class HPBound(val target: HPExpr, val bound: HPConstraint) extends Bound {
  /*
  def composeBound(composed: HPConstraint): Either[Error, HPConstraint] = (this.bound, composed) match {
    case (HPConstraint.Eqn(HPConstraint.ExprEqual(origin)), HPConstraint.Eqn(HPConstraint.ExprEqual(composed))) =>
      if (origin.isSameExpr(composed)) Right(this.bound)
      else Left(???)
    case (HPConstraint.Eqn(HPConstraint.ConstantEqual(v0)), HPConstraint.Eqn(HPConstraint.ConstantEqual(v1))) =>
      if (v0 == v1) Right(this.bound)
      else Left(???)
    case (HPConstraint.Eqn(_), HPConstraint.Eqn(_)) => Left(???)
    case (_: HPConstraint.Constraint, _: HPConstraint.Eqn) => Left(???)
    case (_: HPConstraint.Eqn, _: HPConstraint.Constraint) => Left(???)
    case (HPConstraint.Constraint(thisExprRange, thisConstRange), HPConstraint.Constraint(thatExprRange, thatConstRange)) =>
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

      val newExprRange = HPConstraint.ExprRange(newMax, newMin, newNEs)
      val newConstRange = HPConstraint.ConstantRange(newCMax, newCMin, newCNE)

      Right(HPConstraint.Constraint(newExprRange, newConstRange))
  }
  */

  override def equals(obj: Any): Boolean = obj match {
    case that: HPBound =>
      this.target.isSameExpr(that.target) &&
        this.bound == that.bound
    case _ => false
  }
}

object HPBound {
  def apply(target: HPExpr, range: HPConstraint): HPBound = new HPBound(target, range)
  def build(bound: HPBoundTree): HPBound = {
    val (mins, remain0) = bound.bounds.collectPartition { case RangeExpr.Min(expr) => expr }
    val (maxs, remain1) = remain0.collectPartition { case RangeExpr.Max(expr) => expr }
    val exprEQs = remain1.map { case RangeExpr.EQ(expr) => expr }

    exprEQs match {
      case eqs @ Vector(_, _*) => HPBound(bound.target, HPConstraint.Eqn(eqs))
      case _ =>
        val (constMaxs, exprMaxs) = maxs.collectPartition { case IntLiteral(value) => value }
        val (constMins, exprMins) = mins.collectPartition { case IntLiteral(value) => value }

        val max = exprMaxs.unique ++ constMaxs.minOption.map(IntLiteral(_, Position.empty))
        val min = exprMins.unique ++ constMins.maxOption.map(IntLiteral(_, Position.empty))

        HPBound(bound.target, HPConstraint.Range(max, min))
    }
  }

  def verifyForm(trees: Vector[HPBound], position: Position)(implicit global: GlobalData): Either[Error, Unit] = {
    def verifyTarget: Either[Error, Unit] = {
      val errs = trees.map(bound => bound.target)
        .map(_.extractConstant)
        .collect{ case (_, Some(lit)) => Error.LiteralOnTarget(lit, position) }

      if(errs.isEmpty) Right(())
      else Left(Error.MultipleErrors(errs: _*))
    }

    def verifyEachType: Either[Error, Unit] = {
      val targetErrs = trees.map(tree => tree.target)
        .filterNot(_.tpe.isErrorType)
        .filter(_.tpe != Type.numTpe)
        .map(_.tpe.asRefType)
        .map(tpe => Error.RequireSpecificType(tpe, Seq(Type.numTpe), position))

      val constraintExprs = trees
        .map(_.bound)
        .flatMap {
          case HPConstraint.Eqn(exprs) => exprs
          case HPConstraint.Range(max, min) => max ++ min
        }

      val constraintErrs = constraintExprs
        .filterNot(_.tpe.isErrorType)
        .map(_.tpe.asRefType)
        .filter(_ != Type.numTpe)
        .map(tpe => Error.RequireSpecificType(tpe, Seq(Type.numTpe), position))

      val errs = targetErrs ++ constraintErrs

      if(errs.isEmpty) Right(())
      else Left(Error.MultipleErrors(errs: _*))
    }

    def verifyMultipleRangeSet: Either[Error, Unit] = {
      @tailrec def loop(targets: Vector[HPExpr]): Either[Error, Unit] = {
        targets.headOption match {
          case None => Right(())
          case Some(head) =>
            targets.tail.find(_.isSameExpr(head)) match {
              case None => loop(targets.tail)
              case Some(expr) => Left(Error.HPConstraintSetMultitime(expr, position))
            }
        }
      }

      val targets = trees.map(_.target)
      loop(targets)
    }

    for {
      _ <- verifyTarget
      _ <- verifyEachType
      _ <- verifyMultipleRangeSet
    } yield ()
  }

  def typed(expr: HPExpr)(implicit ctx: Context, global: GlobalData): Either[Error, HPExpr] = expr match {
    case bin @ HPBinOp(left, right) => (typed(left), typed(right)) match {
      case (Right(l), Right(r)) => Right(bin.copy(left = l, right = r).setTpe(Type.numTpe))
      case (Left(err0), Left(err1)) => Left(Error.MultipleErrors(err0, err1))
      case (Left(err), _) => Left(err)
      case (_, Left(err)) => Left(err)
    }
    case unary @ HPUnaryOp(ident) => typed(ident).map(ident => unary.copy(operand = ident.asInstanceOf[Ident]).setTpe(ident.tpe))
    case ident @ Ident(name) => ctx.lookup[Symbol.HardwareParamSymbol](name) match {
      case LookupResult.LookupSuccess(symbol) => symbol.tpe match {
        case Type.ErrorType => Right(ident.setSymbol(Symbol.ErrorSymbol).setTpe(Type.ErrorType))
        case tpe: Type.RefType =>
          if (tpe == Type.numTpe) Right(ident.setSymbol(symbol).setTpe(Type.numTpe))
          else Left(Error.RequireSpecificType(tpe, Seq(Type.numTpe), ident.position))
      }
      case LookupResult.LookupFailure(err) =>
        ident.setSymbol(Symbol.ErrorSymbol).setTpe(Type.ErrorType)
        Left(err)
    }
    case lit: IntLiteral => Right(lit.setTpe(Type.numTpe))
    case lit: StringLiteral => Left(Error.RequireSpecificType(Type.strTpe, Seq(Type.numTpe), lit.position))
  }

  def verifyTarget(target: HPExpr): Either[Error, HPExpr] = target match {
    case lit: Literal => Left(Error.LiteralOnTarget(lit, lit.position))
    case HPUnaryOp(expr) => verifyTarget(expr)
    case ident: Ident => Right(ident)
    case bin @ HPBinOp(left, right) =>
      for {
        l <- verifyTarget(left)
        r <- verifyTarget(right)
      } yield bin.copy(left = l, right = r)
  }

  def simplify(originalHPBounds: Vector[HPBound]): Vector[HPBound] = {
    def execSimplify: Vector[HPBound] = {
      def simplifyConstraint(constraint: HPConstraint): HPConstraint = constraint match {
        case HPConstraint.Eqn(expr) => HPConstraint.Eqn(expr.map(_.sort.combine).unique)
        case HPConstraint.Range(maxs, mins) =>
          val simpleMaxs = maxs.map(_.sort.combine)
          val simpleMins = mins.map(_.sort.combine)
          val (constMaxs, exprMaxs) = simpleMaxs.collectPartition { case IntLiteral(value) => value }
          val (constMins, exprMins) = simpleMins.collectPartition { case IntLiteral(value) => value }

          val emaxs = exprMaxs.unique
          val emins = exprMins.unique
          val cmax = if (constMaxs.isEmpty) None else Some(IntLiteral(constMaxs.min, Position.empty))
          val cmin = if (constMins.isEmpty) None else Some(IntLiteral(constMins.max, Position.empty))

          HPConstraint.Range(emaxs ++ cmax, emins ++ cmin)
      }

      originalHPBounds.map {
        bound =>
          val target = bound.target.sort.combine
          val constraint = simplifyConstraint(bound.bound)

          HPBound(target, constraint)
      }
    }

    def aggregate(bounds: Vector[HPBound]): Vector[(HPExpr, Vector[HPConstraint])] = {
      bounds.headOption match {
        case None => Vector.empty
        case Some(bound) =>
          val target = bound.target
          val (filtered, remains) = bounds.partition(_.target.isSameExpr(target))
          val head = (target, filtered.map(_.bound))
          head +: aggregate(remains)
      }
    }

    def execCompose(constraints: Vector[HPConstraint]): HPConstraint = {
      def composeEqn(eqs: Vector[HPConstraint.Eqn]): HPConstraint.Eqn = HPConstraint.Eqn(eqs.flatMap(_.expr).unique)

      def composeRange(ranges: Vector[HPConstraint.Range]): HPConstraint.Range = {
        val collectLit: PartialFunction[HPExpr, Int] = {
          case IntLiteral(value) => value
        }
        val (maxConsts, maxExprs) = ranges.flatMap(_.max).map(_.sort.combine).collectPartition(collectLit)
        val (minConsts, minExprs) = ranges.flatMap(_.min).map(_.sort.combine).collectPartition(collectLit)
        val maxConst = maxConsts.minOption
        val minConst = minConsts.maxOption
        val max = maxExprs.unique ++ maxConst.map(IntLiteral(_, Position.empty))
        val min = minExprs.unique ++ minConst.map(IntLiteral(_, Position.empty))

        HPConstraint.Range(max, min)
      }

      val (rngs, eqns) = constraints.collect {
        case eqn: HPConstraint.Eqn => Right(eqn)
        case rng: HPConstraint.Range => Left(rng)
      }.partitionMap(identity)

      eqns match {
        case Vector() => composeRange(rngs)
        case eqns => composeEqn(eqns)
      }
    }

    aggregate(execSimplify).map { case (target, constraints) => HPBound(target, execCompose(constraints)) }
  }

  /*
  def verifyForm(bound: HPBoundTree)(implicit ctx: Context.NodeContext, global: GlobalData): Either[Error, Unit] = {
    def verifyExpr(expr: HPExpr): Either[Error, HPExpr] = expr match {
      case lit: StringLiteral => Right(lit.setTpe(Type.strTpe))
      case lit: IntLiteral => Right(lit.setTpe(Type.numTpe))
      case ident: Ident => ctx
        .lookup[Symbol.HardwareParamSymbol](ident.name)
        .toEither
        .map(symbol => ident.setSymbol(symbol).setTpe(symbol.tpe))
      case HPBinOp(left, right) =>
        val terms = for {
          typedLeft <- verifyExpr(left)
          typedRight <- verifyExpr(right)
        } yield (typedLeft, typedRight)

        terms.flatMap {
          case (left, right) => (left.tpe, right.tpe) match {
            case (Type.ErrorType, _) => Left(Error.DummyError)
            case (_, Type.ErrorType) => Left(Error.DummyError)
            case (leftTpe: Type.RefType, rightTpe: Type.RefType) =>
              lazy val typedBinOp = HPBinOp(left, right).setTpe(Type.numTpe).setID(expr.id)
              lazy val leftTypeMissMatch = Error.TypeMismatch(Type.numTpe, leftTpe)
              lazy val rightTypeMissMatch = Error.TypeMismatch(Type.numTpe, rightTpe)

              if (leftTpe == Type.numTpe && rightTpe == Type.numTpe) Right(typedBinOp)
              else if (leftTpe != Type.numTpe && rightTpe != Type.numTpe)
                Left(Error.MultipleErrors(leftTypeMissMatch, rightTypeMissMatch))
              else if (leftTpe != Type.numTpe) Left(leftTypeMissMatch)
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
        def verify(expr: HPExpr)(rootPattern: PartialFunction[HPExpr, Either[Error, Range]]): Either[Error, Range] =
          rootPattern.applyOrElse(expr, (expr: HPExpr) => verifyExpr(expr).map(_ => assignedRange))

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
  */

  def swapBounds(swapped: Vector[HPBound], table: Map[Symbol.HardwareParamSymbol, HPExpr]): Vector[HPBound] = {
    def swapBound(hpBound: HPBound): HPBound = {
      val target = hpBound.target.swap(table).sort
      val bound = hpBound.bound match {
        case HPConstraint.Eqn(exprs) => HPConstraint.Eqn(exprs.map(_.swap(table).sort.combine))
        case HPConstraint.Range(max, min) =>
          val swappedMax = max.map(_.swap(table).sort.combine)
          val swappedMin = min.map(_.swap(table).sort.combine)

          HPConstraint.Range(swappedMax, swappedMin)
      }

      HPBound(target, bound)
    }

    swapped.map(swapBound)
  }

  trait DerivedResult {
    def negate: DerivedResult
  }

  object DerivedResult {
    case class Const(const: IInt.Integer) extends DerivedResult {
      override def negate: DerivedResult = {
        val f = DerivedResult.Const.apply _ compose IInt.Integer.apply
        f(-const.value)
      }
    }

    case class Infs(infs: Vector[IInt.Inf]) extends DerivedResult {
      override def negate: DerivedResult = {
        val negated = infs.map(inf => inf.sign -> inf.expr.negate).map { case (sign, expr) => IInt.Inf(sign, expr) }
        DerivedResult.Infs(negated)
      }
    }

    def combine(results: Vector[DerivedResult])(cmp: (Int, Int) => Boolean): DerivedResult = {
      val iints = results.flatMap {
        case DerivedResult.Infs(infs) => infs
        case DerivedResult.Const(const) => Vector(const)
      }

      iints.foldLeft[DerivedResult](DerivedResult.Infs(Vector.empty)) {
        case (DerivedResult.Infs(_), iint: IInt.Integer) => DerivedResult.Const(iint)
        case (c: DerivedResult.Const, _: IInt.Inf) => c
        case (DerivedResult.Infs(infs), iint: IInt.Inf) =>
          val accCount = infs.head.expr.countLeafs
          val curCount = iint.expr.countLeafs

          if (accCount > curCount) DerivedResult.Infs(Vector(iint))
          else if (accCount == curCount) DerivedResult.Infs(infs :+ iint)
          else DerivedResult.Infs(infs)
        case (DerivedResult.Const(IInt.Integer(v0)), IInt.Integer(v1)) =>
          if (cmp(v1, v0)) DerivedResult.Const(IInt.Integer(v1))
          else DerivedResult.Const(IInt.Integer(v0))
      }
    }
  }

  trait DeriveTool {
    def cmp(a: Int, b: Int): Boolean
    def getEdge(edges: Vector[Int]): Option[Int]
    def select(maxs: Vector[HPExpr], mins: Vector[HPExpr]): Vector[HPExpr]
    val sign: Sign
  }

  val forMax = new DeriveTool {
    override def cmp(a: Int, b: Int): Boolean = a < b
    override def getEdge(edges: Vector[Int]): Option[Int] = edges.minOption
    override def select(maxs: Vector[HPExpr], mins: Vector[HPExpr]): Vector[HPExpr] = maxs
    override val sign: Sign = Sign.Pos
  }

  val forMin = new DeriveTool {
    override def cmp(a: Int, b: Int): Boolean = a > b
    override def getEdge(edges: Vector[Int]): Option[Int] = edges.maxOption
    override def select(maxs: Vector[HPExpr], mins: Vector[HPExpr]): Vector[HPExpr] = mins
    override val sign: Sign = Sign.Neg
  }

  def deriveMax(expr: HPExpr, hpBounds: Vector[HPBound]): IInt = deriveIInt(expr, hpBounds, Sign.Pos, forMax, forMin)
  def deriveMin(expr: HPExpr, hpBounds: Vector[HPBound]): IInt = deriveIInt(expr, hpBounds, Sign.Neg, forMin, forMax)
  private def deriveIInt(expr: HPExpr, hpBounds: Vector[HPBound], infSign: Sign, tool: DeriveTool, negTool: DeriveTool): IInt = {
    def makeAllPatterns(exprss: Vector[Vector[HPExpr]]): Vector[Vector[HPExpr]] = {
      def appendHead(heads: Vector[HPExpr], tails: Vector[Vector[HPExpr]]): Vector[Vector[HPExpr]] = {
        for {
          head <- heads
          tail <- tails
        } yield head +: tail
      }

      exprss.headOption match {
        case None => Vector(Vector.empty)
        case Some(heads) => appendHead(heads, makeAllPatterns(exprss.tail))
      }
    }

    def deriveFromExpr(expr: HPExpr, const: Option[Int]): IInt = {
      val table = deriveEdge(expr, hpBounds, Map.empty, tool, negTool)

      table.get(expr) match {
        case Some(DerivedResult.Infs(_)) => IInt.Inf(infSign, expr)
        case Some(DerivedResult.Const(IInt.Integer(v0))) => IInt.Integer(v0 + const.getOrElse(0))
        case None =>
          val (signs, idents) = expr.collectLeafs.collect {
            case ident: Ident => Sign.Pos -> ident
            case HPUnaryOp(ident) => Sign.Neg -> ident
          }.unzip

          val exprss = idents.map(table(_)).map {
            case DerivedResult.Infs(infs) => infs.map(_.expr)
            case DerivedResult.Const(IInt.Integer(const)) => Vector(IntLiteral(const, Position.empty))
          }

          val signedExprss = (exprss zip signs).map {
            case (exprs, Sign.Pos) => exprs
            case (exprs, Sign.Neg) => exprs.map(_.negate)
          }

          val exprs = makeAllPatterns(signedExprss).map {
            pattern =>
              val expr = pattern.foldRight[HPExpr](IntLiteral(const.getOrElse(0), Position.empty)) {
                case (left, right) if left.position.start >= right.position.start => HPBinOp(left, right, left.position)
                case (left, right) => HPBinOp(left, right, Position.empty)
              }
              expr.sort.combine
          }

          tool.getEdge(exprs.collect { case IntLiteral(value) => value }) match {
            case None => IInt.Inf(infSign, expr)
            case Some(value) => IInt.Integer(value + const.getOrElse(0))
          }
      }
    }

    expr.sort.combine match {
      case IntLiteral(value) => IInt.Integer(value)
      case _ =>
        val (split, const) = expr.extractConstant
        deriveFromExpr(split, const.map(_.value))
    }
  }

  private def deriveEdge(expr: HPExpr, hpBounds: Vector[HPBound], table: Map[HPExpr, DerivedResult], tool: DeriveTool, negTool: DeriveTool): Map[HPExpr, DerivedResult] = {
    hpBounds.find(_.target.isSameExpr(expr)) match {
      case None =>
        val negExpr = expr.negate
        hpBounds.find(_.target.isSameExpr(negExpr)) match {
          case None => expr match {
            case ident: Ident =>
              val inf = IInt.Inf(tool.sign, ident)
              val result = DerivedResult.Infs(Vector(inf))
              table.updated(ident, result)
            case unary: HPUnaryOp =>
              val inf = IInt.Inf(tool.sign, unary)
              val result = DerivedResult.Infs(Vector(inf))
              table.updated(unary, result)
            case expr =>
              expr.collectLeafs.foldLeft(table) {
                case (table, expr) if table.contains(expr) => table
                case (table, expr) => deriveEdge(expr, hpBounds, table, tool, negTool)
              }
          }
          case Some(_) =>
            val derivedTable = deriveEdge(negExpr, hpBounds, table, negTool, tool)
            val negated = derivedTable(negExpr).negate
            derivedTable.updated(expr, negated)
        }
      case Some(bound) =>
        val edgeExprs = bound.bound match {
          case HPConstraint.Eqn(expr) => expr
          case HPConstraint.Range(max, min) => tool.select(max, min)
        }

        val (splits, extractConsts) = edgeExprs.map(_.extractConstant).unzip
        val exprConst = tool.getEdge _ apply splits.collect { case IntLiteral(v) => v }
        val (exprs, consts) = (splits zip extractConsts).filterNot { case (expr, _) => expr.isInstanceOf[Literal] }.unzip
        val derivedTable = exprs.foldLeft(table) {
          case (table, expr) if table.contains(expr) => table
          case (table, expr) => deriveEdge(expr, hpBounds, table, tool, negTool)
        }
        val results = (exprs zip consts)
          .map { case (expr, c) => (derivedTable(expr), c) }
          .map {
            case (DerivedResult.Const(IInt.Integer(v0)), const) => DerivedResult.Const(IInt.Integer(v0 + const.map(_.value).getOrElse(0)))
            case (infs: DerivedResult.Infs, None) => infs
            case (DerivedResult.Infs(infs), Some(v)) =>
              val newInfs = infs.map(inf => IInt.Inf(inf.sign, HPBinOp(inf.expr, v, Position.empty).sort.combine))
              DerivedResult.Infs(newInfs)
          }

        val constTemplate = (num: Int) => DerivedResult.Const(IInt.Integer(num))
        val constResult = exprConst map constTemplate
        val result = DerivedResult.combine(results ++ constResult)(negTool.cmp)
        derivedTable.updated(expr, result)
    }
  }


  def verifyMeetBound(swapped: HPBound, callerHPBounds: Vector[HPBound]): Either[Error, Unit] = {
    val targetMax = deriveMax(swapped.target, callerHPBounds)
    val targetMin = deriveMin(swapped.target, callerHPBounds)

    swapped.bound match {
      case HPConstraint.Eqn(exprs) =>
        val (consts, others) = exprs.collectPartition { case IntLiteral(value) => value }
        val errs = others
          .filterNot(_.isSameExpr(swapped.target))
          .map(expr => Error.HPBoundNotEqualExpr(expr, swapped.target, expr.position))

        lazy val targetConst = (targetMax, targetMin) match {
          case (IInt.Integer(max), IInt.Integer(min)) if max == min => Right(max)
          case _ => Left(Error.HPBoundNotDeriveEqualConst(swapped.target, exprs.head.position))
        }

        def verifyConstEq(targetConst: Int): Either[Error, Unit] = {
          val errs = (consts zip exprs)
            .filter{ case (const, _) => const != targetConst }
            .map{ case (const, expr) => Error.HPBoundEqualConstNotMatch(const, targetConst, expr.position) }

          if (errs.isEmpty) Right(())
          else Left(Error.MultipleErrors(errs: _*))
        }

        if (errs.nonEmpty) Left(Error.MultipleErrors(errs: _*))
        else for {
          eqn <- targetConst
          _ <- verifyConstEq(eqn)
        } yield ()
      case HPConstraint.Range(max, min) =>
        def getEdge(iints: Vector[IInt], infSign: Sign)(edge: Vector[Int] => Option[Int]): IInt = {
          val consts = iints.collect { case IInt.Integer(value) => value }
          edge(consts) match {
            case Some(const) => IInt.Integer(const)
            case None => IInt.Inf(infSign, IntLiteral(0, Position.empty))
          }
        }

        val rangeMax = getEdge(max.map(deriveMax(_, callerHPBounds)), Sign.Pos)(_.minOption)
        val rangeMin = getEdge(min.map(deriveMin(_, callerHPBounds)), Sign.Neg)(_.maxOption)
        lazy val isInMax = targetMax <= rangeMax
        lazy val isInMin = targetMin >= rangeMin
        lazy val isCrossMaxMin = rangeMax < rangeMin
        lazy val outOfRange = Left(Error.HPBoundOutOfRange(swapped.target, (rangeMax, rangeMin), (targetMax, targetMin), swapped.target.position))
        lazy val crossRange = Left(Error.HPBoundRangeCross(rangeMax, rangeMin, swapped.target.position))

        if (!isInMax) outOfRange
        else if (!isInMin) outOfRange
        else if (isCrossMaxMin) crossRange
        else Right(())
    }

    /*
    def valueMeetBound(value: Int): Either[Error, Unit] = {
      def error: Left[Error, Unit] = Left(Error.ValueNotMeetHPBound(value, swapped))

      swapped.bound match {
        case HPConstraint.Eqn(HPConstraint.ExprEqual(_)) => error
        case HPConstraint.Eqn(HPConstraint.ConstantEqual(that)) =>
          if (value == that) Right(())
          else error
        case HPConstraint.Constraint(eRange, cRange) =>
          val v = IInt(value)

          def rangeDefinitely(ranges: Vector[HPExpr])(f: (IInt, IInt) => Boolean): Boolean =
            ranges.forall { expr =>
              callerHPBounds.find(_.target.isSameExpr(expr)) match {
                case None => false
                case Some(bound) => bound.bound match {
                  case HPConstraint.Eqn(_: HPConstraint.ExprEqual) => false
                  case HPConstraint.Eqn(HPConstraint.ConstantEqual(that)) => f(IInt(that), v)
                  case HPConstraint.Constraint(_, cRange) => f(cRange.min, v)
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
                  case HPConstraint.Eqn(_: HPConstraint.ExprEqual) => false
                  case HPConstraint.Eqn(HPConstraint.ConstantEqual(that)) => that != value
                  case HPConstraint.Constraint(_, cRange) => cRange.min > v || cRange.max < v
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
          case HPConstraint.Eqn(HPConstraint.ExprEqual(callerExpr)) => swapped.bound match {
            case HPConstraint.Eqn(HPConstraint.ExprEqual(replacedExpr)) =>
              if (replacedExpr.isSameExpr(callerExpr)) Right(())
              else buildError(callerBound)
            case _ => buildError(callerBound)
          }
          case HPConstraint.Eqn(HPConstraint.ConstantEqual(callerValue)) => valueMeetBound(callerValue)
          case HPConstraint.Constraint(callerExprRange, callerConstRange) => swapped.bound match {
            case HPConstraint.Eqn(_) => buildError(callerBound)
            case HPConstraint.Constraint(replacedExprRange, replacedConstRange) =>
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
    */

    /*
    def deriveRange(expr: HPExpr, callerHPBounds: Vector[HPBound]): Either[Error, HPConstraint] = {
      def splitConstant(expr: HPExpr): (HPExpr, Option[(Operation, IntLiteral)]) =
        expr match {
          case ident: Ident => (ident, None)
          case literal: IntLiteral => (literal, None)
          case HPBinOp(op, left, right: IntLiteral) => (left, Some(op, right))
          case binop: HPBinOp => (binop, None)
        }

      def buildFromConstEq(equal: HPConstraint.ConstantEqual)(f: IInt => IInt): Either[Error, HPConstraint] = {
        f(IInt(equal.num)) match {
          case IInt.Integer(value) => Right(HPConstraint.Eqn(HPConstraint.ConstantEqual(value)))
          case _ => Left(???)
        }
      }

      def buildFronConstRange(range: HPConstraint.ConstantRange)(f: IInt => IInt): Either[Error, HPConstraint] = {
        val range0 = f(range.max)
        val range1 = f(range.min)

        if (range0 == range1) {
          range0 match {
            case IInt.Integer(value) =>
              val constEq = HPConstraint.ConstantEqual(value)
              Right(HPConstraint.Eqn(constEq))
            case _ => Left(???) // Constant Equal but Positive Inf or Negative Inf is error
          }
        } else {
          val (max, min) =
            if (range0 > range1) (range0, range1)
            else (range1, range0)

          val ne = range.ne
            .map(value => f(IInt(value)))
            .collect { case IInt.Integer(value) => value }

          val exprRange = HPConstraint.ExprRange(Vector.empty, Vector.empty, Vector.empty)
          val constRange = HPConstraint.ConstantRange(max, min, ne)
          Right(HPConstraint.Constraint(exprRange, constRange))
        }
      }

      def constructRange(expr: HPExpr): Either[Error, HPConstraint] = {
        def getOperand(expr: HPConstraint): Vector[IInt] = expr match {
          case HPConstraint.Constraint(_, HPConstraint.ConstantRange(max, min, _)) => Vector(max, min)
          case HPConstraint.Eqn(HPConstraint.ConstantEqual(value)) => Vector(IInt(value))
        }

        def selectEdge(values: Vector[IInt])(f: (IInt, IInt) => Boolean): IInt = {
          values.tail.foldLeft(values.head) {
            case (remain, edge) =>
              if (f(edge, remain)) edge
              else remain
          }
        }

        def calcRange(left: HPConstraint, right: HPConstraint, op: Operation): Either[Error, HPConstraint] = {
          val lefts = getOperand(left)
          val rights = getOperand(right)

          val operands = for {
            l <- lefts
            r <- rights
          } yield (l, r)

          val f: (IInt, IInt) => IInt = op match {
            case Operation.Add => _ + _
            case Operation.Sub => _ - _
          }

          val values = operands.map { case (l, r) => f(l, r) }
          val max = selectEdge(values)(_ > _)
          val min = selectEdge(values)(_ < _)

          if (max != min) Right(HPConstraint.Constraint(HPConstraint.Range.empty, HPConstraint.ConstantRange(max, min, Set.empty)))
          else max match {
            case IInt.Integer(value) => Right(HPConstraint.Eqn(HPConstraint.ConstantEqual(value)))
            case _ => Left(???)
          }
        }

        def loop(expr: HPExpr): Either[Error, HPConstraint] = {
          expr match {
            case IntLiteral(value) => Right(HPConstraint.Eqn(HPConstraint.ConstantEqual(value)))
            case ident: Ident =>
              val range = callerHPBounds
                .find(_.target.isSameExpr(ident))
                .map(_.bound)
                .filterNot(_.isInstanceOf[HPConstraint.ExprEqual])
                .getOrElse(HPConstraint.Constraint.empty)

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
              case HPConstraint.Eqn(eq: HPConstraint.ConstantEqual) => buildFromConstEq(eq)(f)
              case HPConstraint.Eqn(_) => Right(HPConstraint.Constraint.empty)
              case HPConstraint.Constraint(_, consts) => buildFronConstRange(consts)(f)
            }
        }
      }
    }
    swapped.target match {
      case IntLiteral(value) => valueMeetBound(value)
      case expr: HPExpr => exprMeetBound(expr)
    }
    */
  }
}

trait HPConstraint
object HPConstraint {
  case class Range(max: Vector[HPExpr], min: Vector[HPExpr]) extends HPConstraint {
    override def equals(obj: Any): Boolean = {
      def loop(thisExprs: Vector[HPExpr], thatExprs: Vector[HPExpr]): Boolean = {
        (thisExprs, thatExprs) match {
          case (Vector(), Vector()) => true
          case (Vector(), _) => false
          case (_, Vector()) => false
          case (exprs0, exprs1) =>
            val expr = exprs0.head
            val remains = exprs1.filterNot(_.isSameExpr(expr))

            loop(exprs0.tail, remains)
        }
      }

      obj match {
        case that: HPConstraint.Range => loop(this.max, that.max) && loop(this.min, that.min)
        case _ => false
      }
    }
  }

  object Range {
    def empty: HPConstraint.Range = HPConstraint.Range(Vector.empty, Vector.empty)
  }

  case class Eqn(expr: Vector[HPExpr]) extends HPConstraint {
    override def equals(obj: Any): Boolean = {
      def loop(thisExprs: Vector[HPExpr], thatExprs: Vector[HPExpr]): Boolean = {
        (thisExprs, thatExprs) match {
          case (Vector(), Vector()) => true
          case (Vector(), _) => false
          case (_, Vector()) => false
          case (exprs0, exprs1) =>
            val expr = exprs0.head
            val remains = exprs1.filterNot(_.isSameExpr(expr))

            loop(exprs0.tail, remains)
        }
      }

      obj match {
        case that: HPConstraint.Eqn => loop(this.expr, that.expr)
        case _ => false
      }
    }
  }

  def empty: HPConstraint.Range = Range.empty
  def isOverlapped(constraint0: HPConstraint, constraint1: HPConstraint, bounds0: Vector[HPBound], bounds1: Vector[HPBound]): Boolean = {
    def deriveEdge(constraint: HPConstraint, bounds: Vector[HPBound]): (IInt, IInt) = {
      def rangeEdge(exprs: Vector[HPExpr], sign: Sign)(edge: Vector[Int] => Option[Int]): IInt = {
        val (_, others) = exprs.map(HPBound.deriveMax(_, bounds)).partition(_.isInf)
        val constEdge = edge apply others.map(_.asInstanceOf[IInt.Integer]).map{ case IInt.Integer(v) => v }

        constEdge match {
          case None => IInt.Inf(sign, IntLiteral(0, Position.empty)) // use int literal for now, but this is subject to fix
          case Some(const) => IInt.Integer(const)
        }
      }

      val (maxs, mins) = constraint match {
        case HPConstraint.Range(maxs, mins) => (maxs, mins)
        case HPConstraint.Eqn(exprs) =>(exprs, exprs)
      }

      val max = rangeEdge(maxs, Sign.Pos)(_.minOption)
      val min = rangeEdge(mins, Sign.Neg)(_.maxOption)
      (max, min)
    }

    val (max0, min0) = deriveEdge(constraint0, bounds0)
    val (max1, min1) = deriveEdge(constraint1, bounds1)

    (max0 >= max1 && min0 <= max1) ||
    (max0 >= min1 && min0 <= min1) ||
    (max0 >= max1 && min0 <= min1) ||
    (max0 <= max1 && min0 >= min1)
  }
}

