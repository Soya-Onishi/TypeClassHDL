package tchdl.typecheck

import java.lang.invoke.ConstantCallSite

import tchdl.ast._
import tchdl.util.TchdlException.ImplementationErrorException
import tchdl.util.{Constraint, Context, Error, HPRange, HasImpls, LookupResult, RangeEdge, Reporter, Scope, Symbol, Type}

import scala.annotation.tailrec
import scala.reflect.ClassTag
import scala.reflect.runtime.universe.TypeTag

// TODO:
//   Add logic to verify whether all type parameters are used at signature
//   e.g. impl[A, B] Interface[A] for Type[B] is valid.
//        However, impl[A, B] Interface[A] for Type is invalid(B is not used).
object ImplVerifier {
  type TopLevelDefinition = {
    val hp: Vector[ValDef]
    val tp: Vector[TypeDef]
    val bounds: Vector[Bound]
    def symbol: Symbol
  }

  def exec(cu: CompilationUnit) = ???

  def buildRefType[SymbolType <: Symbol.TypeSymbol : TypeTag : ClassTag](tpe: TypeTree, ctx: Context.NodeContext): Either[Error, Type.RefType] = {
    val typedTpe = Typer.typedTypeTree(tpe)(ctx, acceptPkg = false)
    TypedCache.setTree(typedTpe)

    typedTpe.tpe match {
      case tpe: Type.RefType => tpe.origin match {
        case _: SymbolType => Right(tpe)
        case origin => Left(Error.RequireSymbol[SymbolType](origin))
      }
      case Type.ErrorType => Left(Error.DummyError)
    }
  }

  trait WhereClause
  object WhereClause {
    case class TP(tp: Symbol.TypeParamSymbol, interfaces: Vector[Type.RefType]) extends WhereClause
    case class HP(hp: HPExpr, constraints: Vector[ConstraintExpr]) extends WhereClause
  }

  def setBound(bound: Bound)(implicit ctx: Context.NodeContext): Either[Error, WhereClause] = {
    def setBoundForTP(bound: TPBound): Either[Error, WhereClause.TP] =
      ctx.lookup[Symbol.TypeParamSymbol](bound.target) match {
        case LookupResult.LookupFailure(err) =>
          Left(err)
        case LookupResult.LookupSuccess(symbol) if symbol.owner != ctx.owner =>
          Left(Error.SetBoundForDifferentOwner(symbol.owner, ctx.owner))
        case LookupResult.LookupSuccess(symbol) =>
          val (errs, constraints) =
            bound.constraints
              .map(buildRefType[Symbol.InterfaceSymbol](_, ctx))
              .partitionMap(e => e)

          val tpClause = WhereClause.TP(symbol, constraints)
          if(errs.isEmpty) Right(tpClause)
          else Left(Error.MultipleErrors(errs))
      }

    def setBoundForHP(bound: HPBound): Either[Error, WhereClause.HP] = {
      def verifyTarget(target: HPExpr): Either[Error, HPExpr] = {
        def verifyHPBinOp(binop: HPBinOp): Either[Error, HPExpr] = {
          def verifyChild(child: Either[Error, HPExpr]): Either[Error, HPExpr] =
            child match {
              case Left(err) => Left(err)
              case Right(left) => left.tpe match {
                case Type.ErrorType => Right(left)
                case tpe: Type.RefType if tpe =:= Type.numTpe => Right(left)
                case tpe => Left(???)
              }
            }

          val HPBinOp(operator, left, right) = binop
          val leftResult = verifyChild(loop(left, isRoot = false))
          val rightResult = verifyChild(loop(right, isRoot = false))

          (leftResult, rightResult) match {
            case (Left(left), Left(right)) => Left(Error.MultipleErrors(Vector(left, right)))
            case (Left(err), _) => Left(err)
            case (_, Left(err)) => Left(err)
            case (Right(left), Right(right)) =>
              Right(HPBinOp(operator, left, right).setTpe(Type.numTpe).setID(binop.id))
          }
        }

        def verifyIdentity(ident: Ident): Either[Error, Ident] = {
          val Ident(name) = ident

          ctx.lookup[Symbol.HardwareParamSymbol](name) match {
            case LookupResult.LookupFailure(err) => Left(err)
            case LookupResult.LookupSuccess(symbol) if symbol.owner != ctx.owner => Left(???)
            case LookupResult.LookupSuccess(symbol) =>
              def succeed(tpe: Type): Either[Error, Ident] =
                Right(Ident(name).setTpe(tpe).setSymbol(symbol).setID(ident.id))

              symbol.tpe match {
                case Type.ErrorType => succeed(Type.ErrorType)
                case tpe: Type.RefType if tpe =:= Type.numTpe => succeed(tpe)
                case tpe => Left(???)
              }
          }
        }

        def verifyIntLiteral(lit: IntLiteral, isRoot: Boolean): Either[Error, IntLiteral] =
          if(isRoot) Left(???)
          else Right(lit)

        def loop(expr: HPExpr, isRoot: Boolean): Either[Error, HPExpr] =
          expr match {
            case int: IntLiteral => verifyIntLiteral(int, isRoot)
            case _: StringLiteral => Left(???)
            case binop: HPBinOp => verifyHPBinOp(binop)
            case ident: Ident => verifyIdentity(ident)
          }

        loop(target, isRoot = true)
      }

      def verifyConstraint(constraint: ConstraintExpr): Either[Error, ConstraintExpr] = {
        def buildConstraint(expr: HPExpr): Right[Error, ConstraintExpr] = {
          val c = constraint match {
            case _: ConstraintExpr.EQ => ConstraintExpr.EQ(expr)
            case _: ConstraintExpr.NE => ConstraintExpr.NE(expr)
            case _: ConstraintExpr.LT => ConstraintExpr.LT(expr)
            case _: ConstraintExpr.LE => ConstraintExpr.LE(expr)
            case _: ConstraintExpr.GT => ConstraintExpr.GT(expr)
            case _: ConstraintExpr.GE => ConstraintExpr.GE(expr)
          }

          Right(c)
        }

        constraint.expr match {
          case int: IntLiteral => buildConstraint(int)
          case ident @ Ident(name) => ctx.lookup[Symbol.HardwareParamSymbol](name) match {
            case LookupResult.LookupFailure(err) => Left(err)
            case LookupResult.LookupSuccess(symbol) =>
              val verified = Ident(name).setTpe(Type.numTpe).setSymbol(symbol).setID(ident.id)
              buildConstraint(verified)
          }
        }
      }

      val sortedTarget = bound.target.sort

      val verifiedTarget = verifyTarget(sortedTarget)
      val (errs, verifiedConstraints) = bound.constraints
        .map(verifyConstraint)
        .partitionMap(identity)

      (verifiedTarget, errs) match {
        case (Right(target), Vector()) => Right(WhereClause.HP(target, verifiedConstraints))
        case (Left(err), errs) => Left(Error.MultipleErrors(err +: errs))
      }
    }

    bound match {
      case bound: TPBound => setBoundForTP(bound)
      case bound: HPBound => setBoundForHP(bound)
    }
  }

  def setBoundsForTopDefinition(definition: TopLevelDefinition)(implicit ctx: Context.RootContext): Unit = {
    definition.symbol.tpe // run Namer for hardwareParam, typeParam and components

    val signatureCtx = Context(ctx, definition.symbol)
    signatureCtx.reAppend(
      definition.hp.map(_.symbol) ++
      definition.tp.map(_.symbol) : _*
    )

    definition.bounds.foreach(setBound(_)(signatureCtx))
  }

  def implementInterface(impl: ImplementInterface)(implicit ctx: Context.RootContext): Unit = {
    val signatureCtx = Context(ctx, impl.symbol)
    impl.hp.foreach(Namer.nodeLevelNamed(_, signatureCtx))
    impl.tp.foreach(Namer.nodeLevelNamed(_, signatureCtx))

    val (errs, bounds) = impl.bounds
      .map(setBound(_)(signatureCtx))
      .partitionMap(identity)
    val (tps, hps) = bounds.foldLeft((Vector.empty[WhereClause.TP], Vector.empty[WhereClause.HP])) {
      case ((tps, hps), tp: WhereClause.TP) => (tps :+ tp, hps)
      case ((tps, hps), hp: WhereClause.HP) => (tps, hps :+ hp)
    }

    tps.foreach(tp => tp.tp.setBounds(tp.interfaces))
    signatureCtx.owner.setHPBounds(hps.map(hp => HPBound(hp.hp, hp.constraints)))
    Reporter.appendError(Error.MultipleErrors(errs))

    val interface = buildRefType[Symbol.InterfaceSymbol](impl.interface, signatureCtx)
    val target = buildRefType[Symbol.ClassTypeSymbol](impl.target, signatureCtx)

    (interface, target) match {
      case (Left(err), _) => Reporter.appendError(err)
      case (_, Left(err)) => Reporter.appendError(err)
      case (Right(interface), Right(target)) =>
        val implCtx = Context(ctx, impl.symbol, target)
        impl.methods.foreach(Namer.nodeLevelNamed(_, implCtx))

        val container = ImplementInterfaceContainer(impl, ctx, interface, target, implCtx.scope)
        interface.origin.asInterfaceSymbol.appendImpl(impl, container)

        SymbolBuffer.append(interface.origin.asInterfaceSymbol)
    }
  }

  def implementClass(impl: ImplementClass)(implicit ctx: Context.RootContext): Unit = {
    val signatureCtx = Context(ctx, impl.symbol)
    impl.hp.foreach(Namer.nodeLevelNamed(_, signatureCtx))
    impl.tp.foreach(Namer.nodeLevelNamed(_, signatureCtx))
    impl.bounds.foreach(setBound(_)(signatureCtx))

    val tpe = buildRefType[Symbol.ClassTypeSymbol](impl.target, signatureCtx)

    tpe match {
      case Left(err) => Reporter.appendError(err)
      case Right(tpe) =>
        val implCtx = Context(signatureCtx, impl.symbol, tpe)
        impl.methods.foreach(Namer.nodeLevelNamed(_, implCtx))
        impl.stages.foreach(Namer.nodeLevelNamed(_, implCtx))

        val container = ImplementClassContainer(impl, ctx, tpe, implCtx.scope)

        tpe.origin match {
          case clazz: Symbol.ClassTypeSymbol =>
            clazz.appendImpl(impl, container)
            SymbolBuffer.append(clazz)
          case symbol =>
            val msg = s"expect struct symbol or module symbol, actual[${symbol.getClass}]"
            throw new ImplementationErrorException(msg)
        }
    }
  }

  def impls(defTree: Definition)(implicit ctx: Context.RootContext): Unit =
    defTree match {
      case module: ModuleDef => setBoundsForTopDefinition(module)
      case struct: StructDef => setBoundsForTopDefinition(struct)
      case interface: InterfaceDef => setBoundsForTopDefinition(interface)
      case impl: ImplementInterface => implementInterface(impl)
      case impl: ImplementClass => implementClass(impl)
      case _ =>
    }
}

object SymbolBuffer {
  import scala.collection.mutable

  private val interfaces = mutable.HashSet[Symbol.InterfaceSymbol]()
  private val types = mutable.HashSet[Symbol.ClassTypeSymbol]()

  def append(symbol: Symbol.ClassTypeSymbol): Unit = types += symbol
  def append(symbol: Symbol.InterfaceSymbol): Unit = interfaces += symbol

  def verify(): Unit = {
    def verifyHps(impl: Symbol.ImplementSymbol, hps: Vector[Expression], ctx: Context.RootContext): Unit = {
      val implCtx = Context(ctx, impl)

      hps.foreach { hp => Typer.typedExpr(hp)(implCtx) }
    }

    def verifyAllImpls[T <: HasImpls](sets: mutable.HashSet[T])(verifier: T#ImplType => Unit): Unit =
      sets.foreach(_.impls.foreach(verifier))

    verifyAllImpls(interfaces){
      impl =>
        verifyHps(impl.symbol, impl.targetInterface.hardwareParam, impl.ctx)
        verifyHps(impl.symbol, impl.targetType.hardwareParam, impl.ctx)
    }

    verifyAllImpls(types){
      impl =>
        verifyHps(impl.symbol, impl.targetType.hardwareParam, impl.ctx)
    }
  }

  def verifyImplConflict(): Unit = {
    def verifySameForm(tpe0: Type.RefType, tpe1: Type.RefType): Option[Type.RefType] = {
      (tpe0.origin, tpe1.origin) match {
        case (_: Symbol.TypeParamSymbol, _: Symbol.TypeParamSymbol) => Some(tpe0)
        case (_: Symbol.EntityTypeSymbol, _: Symbol.EntityTypeSymbol) =>
          val tps = tpe0.typeParam
            .zip(tpe1.typeParam)
            .map{ case (t0, t1) => verifySameForm(t0, t1) }

          if(tps.exists(_.isEmpty)) None
          else Some(Type.RefType(tpe0.origin, tpe0.hardwareParam, tps.flatten))
        case (_: Symbol.EntityTypeSymbol, _: Symbol.TypeParamSymbol) if tpe0 <|= tpe1 => Some(tpe0)
        case (_: Symbol.TypeParamSymbol, _: Symbol.EntityTypeSymbol) if tpe1 <|= tpe0 => Some(tpe1)
        case (_, _) => None
      }
    }

    /**
     * This function insert RefType that has entity type origin into
     * RefType that has type parameter origin.
     *
     * E.g.
     *    impl0: impl[A1, B1] Interface[ST[A1]] for Type[B1]
     *    impl1: impl[A2, B2] Interface[A2] for Type[ST[B2]]
     *                        ↓
     *    impl0: impl[A1]     Interface[ST[A1]] for Type[ST[B2]]
     *    impl1: impl[A2, B2] Interface[A2]     for Type[ST[B2]]
     *
     *    map will have one pair (B1 -> ST[B2]) in this case
     * @param impl0 impl that has types which are replaced from type parameter into entity type
     * @param impl1 impl that has types which are used to replace impl0's type parameter
     * @param map   table of (type parameters -> entity type)
     * @param tpes  this function used to get all types impl has
     * @tparam T    ImplementContainer
     */
    def insertRefType[T <: ImplementContainer](
      impl0: T,
      impl1: T,
      map: mutable.Map[Symbol.TypeParamSymbol, Option[Type.RefType]]
    )(
      tpes: T => Vector[Type.RefType]
    ): Unit = {
      def inner(tpe0: Type.RefType, tpe1: Type.RefType): Vector[(Symbol.TypeParamSymbol, Type.RefType)] = {
        (tpe0.origin, tpe1.origin) match {
          case (t: Symbol.TypeParamSymbol, _) if tpe1 <|= tpe0 => Vector(t -> tpe1)
          case (t0: Symbol.EntityTypeSymbol, t1: Symbol.EntityTypeSymbol) if t0 == t1 =>
            tpe0.typeParam
              .zip(tpe1.typeParam)
              .flatMap{ case (t0, t1) => inner(t0, t1) }
          case (_, _) => Vector.empty
        }
      }

      val tab = map.collect { case (key, Some(value)) => key -> value }.toMap
      val vec = tpes(impl0)
        .zip(tpes(impl1))
        .map{ case (tpe0, tpe1) => (tpe0.replaceWithMap(tab), tpe1.replaceWithMap(tab)) }
        .flatMap{ case (tpe0, tpe1) => inner(tpe0, tpe1) }

      vec.groupBy(_._1)
        .map{ case (key, pairs) => key -> pairs.head._2 }
        .foreach{ case (key, value) => map(key) = Some(value) }
    }

    @tailrec
    def verifyClassImplConflict(impls: Vector[ImplementClassContainer]): Unit = {
      def verify(impl0: ImplementClassContainer, impl1: ImplementClassContainer): Either[Error, Unit] = {
        val typeParamMap = mutable.Map(
          impl0.typeParam.map(_ -> Option.empty[Type.RefType]) ++
            impl1.typeParam.map(_ -> Option.empty[Type.RefType]): _*
        )

        insertRefType(impl0, impl1, typeParamMap)(impl => Vector(impl.targetType))
        insertRefType(impl1, impl0, typeParamMap)(impl => Vector(impl.targetType))

        val replaceMap = typeParamMap.collect { case (key, Some(value)) => key -> value }.toMap

        val result = verifySameForm(
          impl0.targetType.replaceWithMap(replaceMap),
          impl1.targetType.replaceWithMap(replaceMap)
        )

        result match {
          case Some(tpe) => Left(Error.ImplementClassConflict(tpe))
          case None => Right(())
        }
      }

      impls.tail
        .map(verify(impls.head, _))
        .collect{ case Left(err) => err }
        .foreach(Reporter.appendError)

      verifyClassImplConflict(impls.tail)
    }

    @tailrec
    def verifyInterfaceImplConflict(impls: Vector[ImplementInterfaceContainer]): Unit = {
      def verify(impl0: ImplementInterfaceContainer, impl1: ImplementInterfaceContainer): Either[Error, Unit] = {
        val typeParamMap = mutable.Map(
          impl0.typeParam.map(_ -> Option.empty[Type.RefType]) ++
            impl1.typeParam.map(_ -> Option.empty[Type.RefType]): _*
        )

        insertRefType(impl0, impl1, typeParamMap)(impl => Vector(impl.targetInterface, impl.targetType))
        insertRefType(impl1, impl0, typeParamMap)(impl => Vector(impl.targetInterface, impl.targetType))

        val replaceMap = typeParamMap
          .collect{ case (key, Some(value)) => key -> value}
          .toMap

        val interface =
          verifySameForm(
            impl0.targetInterface.replaceWithMap(replaceMap),
            impl1.targetInterface.replaceWithMap(replaceMap)
          )

        val target =
          verifySameForm(
            impl0.targetType.replaceWithMap(replaceMap),
            impl1.targetType.replaceWithMap(replaceMap)
          )

        (interface, target) match {
          case (Some(i), Some(t)) => Left(Error.ImplementInterfaceConflict(i, t))
          case (_, _) => Right(())
        }
      }

      impls.tail
        .map(verify(impls.head, _))
        .collect{ case Left(err) => err }
        .foreach(Reporter.appendError)

      verifyInterfaceImplConflict(impls.tail)
    }

    interfaces.foreach(interface => verifyInterfaceImplConflict(interface.impls))
    types.foreach(tpe => verifyClassImplConflict(tpe.impls))
  }
}

abstract class ImplementContainer {
  type TreeType <: Definition

  val ctx: Context.RootContext
  val targetType: Type.RefType
  val scope: Scope
  val symbol: Symbol.ImplementSymbol
  val id: Int
  val typeParam: Vector[Symbol.TypeParamSymbol]
  val hardwareParam: Vector[Symbol.HardwareParamSymbol]

  def isValid: Boolean
  final def lookup[T <: Symbol : ClassTag : TypeTag](name: String): Option[T] =
    scope.lookup(name).collect{ case symbol: T => symbol }

  def signature: String
}


abstract class ImplementInterfaceContainer(
  val ctx: Context.RootContext,
  val targetInterface: Type.RefType,
  val targetType: Type.RefType,
  val scope: Scope
) extends ImplementContainer {
  override type TreeType = ImplementInterface

  override def isValid: Boolean = {
    val nodeCtx = Context(ctx, symbol)
    val beforeCounts = Reporter.errorCounts

    def typedHardwareParam(hps: Vector[Expression]): Unit = {
      hps.foreach {
        hp =>
          TypedCache.getTree(hp) match {
            case Some(_) =>
            case None =>
              val typedHp = Typer.typedExpr(hp)(nodeCtx)
              TypedCache.setTree(typedHp)
          }
      }
    }

    typedHardwareParam(targetInterface.hardwareParam)
    typedHardwareParam(targetType.hardwareParam)

    val afterCounts = Reporter.errorCounts
    beforeCounts == afterCounts
  }

  override def signature: String = s"impl $targetInterface for $targetType"
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
}

abstract class ImplementClassContainer(
  val ctx: Context.RootContext,
  val targetType: Type.RefType,
  val scope: Scope
) extends ImplementContainer {
  override type TreeType = ImplementClass

  override def isValid: Boolean = {
    val nodeCtx = Context(ctx, symbol)
    val beforeCounts = Reporter.errorCounts

    targetType.hardwareParam.foreach {
      hp =>
        TypedCache.getTree(hp) match {
          case Some(_) =>
          case None =>
            val typedHp = Typer.typedExpr(hp)(nodeCtx)
            TypedCache.setTree(typedHp)
        }
    }

    def afterCounts = Reporter.errorCounts

    beforeCounts == afterCounts
  }

  override def signature: String = s"impl $targetType"
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
}

