package tchdl.typecheck

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

  def setBound(bound: Bound)(implicit ctx: Context.NodeContext): Unit = {
    def setBoundForTP(bound: TypeParamBound): Unit =
      ctx.lookup[Symbol.TypeParamSymbol](bound.target) match {
        case LookupResult.LookupFailure(err) => Reporter.appendError(err)
        case LookupResult.LookupSuccess(symbol) if symbol.owner != ctx.owner =>
          Reporter.appendError(Error.SetBoundForDifferentOwner(symbol.owner, ctx.owner))
        case LookupResult.LookupSuccess(symbol) =>
          val (errs, constraints) =
            bound.constraints
              .map(buildRefType[Symbol.InterfaceSymbol](_, ctx))
              .partitionMap(e => e)

          errs.foreach(Reporter.appendError)
          symbol.setBounds(constraints)
      }

    def setBoundForHP(bound: HardwareParamBound): Unit = {
      def getSubjects(expr: Expression with HardwareParam): Either[Error, Set[Symbol.HardwareParamSymbol]] = expr match {
        case HPBinOp(_, left, right) => (getSubjects(left), getSubjects(right)) match {
          case (Right(left), Right(right)) => Right(left ++ right)
          case (Left(left), Left(right)) => Left(Error.MultipleErrors(Seq(left, right)))
          case (Left(err), _) => Left(err)
          case (_, Left(err)) => Left(err)
        }
        case Ident(name) => ctx.lookup[Symbol.HardwareParamSymbol](name) match {
          case LookupResult.LookupFailure(err) => Left(err)
          case LookupResult.LookupSuccess(sym) if sym.owner != ctx.owner => Left(???)
          case LookupResult.LookupSuccess(sym) => Right(Set(sym))
        }
      }

      def verifyConstraints(): Either[Error, HPRange] = {
        def verifyConstraints(expr: ConstraintExpr): Either[Error, HPRange] = expr match {
          case ConstraintExpr.Equal(Ident(_)) => Left(???) // TODO: Add error representing identity is not allowed
          case ConstraintExpr.Equal(int: IntLiteral) => Right(HPRange(RangeEdge.ThanEq(int), RangeEdge.ThanEq(int)))
          case ConstraintExpr.LessEq(expr) => Right(HPRange(RangeEdge.Inf, RangeEdge.ThanEq(expr)))
          case ConstraintExpr.LessThan(expr) => Right(HPRange(RangeEdge.Inf, RangeEdge.Than(expr)))
          case ConstraintExpr.GreaterEq(expr) => Right(HPRange(RangeEdge.ThanEq(expr), RangeEdge.Inf))
          case ConstraintExpr.GreaterThan(expr) => Right(HPRange(RangeEdge.Than(expr), RangeEdge.Inf))
        }

        val constraints = bound.constraints.map(verifyConstraints)

        val range = constraints
          .foldLeft[Either[Vector[Error], HPRange]](Right(HPRange(RangeEdge.Inf, RangeEdge.Inf))) {
            case (Right(_), Left(err)) => Left(Vector(err))
            case (Left(errs), Right(_)) => Left(errs)
            case (Left(errs), Left(err)) => Left(errs :+ err)
            case (Right(ranges), Right(range)) => ranges.unify(range).left.map(err => Vector(err))
          }

        range.left.map(errs => Error.MultipleErrors(errs))
      }

      def setRange(expr: Expression with HardwareParam)(setter: (Symbol.HardwareParamSymbol, HPRange) => Either[Error, Unit]): Unit = {
        val subjects = getSubjects(expr)
        val range = verifyConstraints()

        (subjects, range) match {
          case (Right(subjects), Right(range)) =>
            val result = subjects.iterator
              .map(setter(_, range))
              .foldLeft[Either[Vector[Error], Unit]](Right(())) {
                case (Right(()), Right(())) => Right(())
                case (Right(()), Left(err)) => Left(Vector(err))
                case (Left(errs), Right(())) => Left(errs)
                case (Left(errs), Left(err)) => Left(errs :+ err)
              }

            result.left.foreach{
              errs => Reporter.appendError(Error.MultipleErrors(errs))
            }
          case (Left(subjectErr), Left(constraintErr)) =>
            Reporter.appendError(subjectErr)
            Reporter.appendError(constraintErr)
          case (Left(err), _) => Reporter.appendError(err)
          case (_, Left(err)) => Reporter.appendError(err)
        }
      }

      bound.target match {
        case _: StringLiteral => Reporter.appendError(???) // TODO: Add error that represents literal is not allowed here
        case _: IntLiteral => Reporter.appendError(???) // TODO: Add error that represents literal is not allowed here
        case id: Ident => setRange(id){ case (sym, range) => sym.setRange(range) }
        case expr: HPBinOp =>
          val sortedExpr = expr.sort
          setRange(expr) {
            case (sym, range) => sym.appendBound(Constraint(sortedExpr, range))
          }
      }
    }

    bound match {
      case bound: TypeParamBound => setBoundForTP(bound)
      case bound: HardwareParamBound => setBoundForHP(bound)
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
    impl.bounds.foreach(setBound(_)(signatureCtx))

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
    }
}

