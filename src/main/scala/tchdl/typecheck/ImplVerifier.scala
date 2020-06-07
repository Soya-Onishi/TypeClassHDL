package tchdl.typecheck

import tchdl.ast._
import tchdl.util.{Context, Error, HasImpls, Reporter, Scope, Symbol, Type, Bound, TPBound, HPBound}

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
    val bounds: Vector[BoundTree]
    def symbol: Symbol
  }

  def exec(cu: CompilationUnit) = ???

  def setBound(bound: BoundTree)(implicit ctx: Context.NodeContext): Either[Error, Bound] = {
    def setBoundForTP(bound: TPBoundTree): Either[Error, TPBound] = {
      val (targetErrs, target) = TPBound.buildTarget(bound.target)
      val (boundsErrs, bounds) = TPBound.buildBounds(bound.bounds)

      val errs = Vector(targetErrs ++ boundsErrs).flatten
      if(errs.nonEmpty) Left(Error.MultipleErrors(errs: _*))
      else Right(TPBound(TPBoundTree(target, bounds)))
    }

    def setBoundForHP(bound: HPBoundTree): Either[Error, HPBound] = {
      HPBound.verifyForm(bound) match {
        case Right(_) => Right(HPBound(bound))
        case Left(err) => Left(err)
      }
    }

    bound match {
      case bound: TPBoundTree => setBoundForTP(bound)
      case bound: HPBoundTree => setBoundForHP(bound)
    }
  }

  def setBoundsForTopDefinition(definition: TopLevelDefinition)(implicit ctx: Context.RootContext): Unit = {
    definition.symbol.tpe // run Namer for hardwareParam, typeParam and components

    val signatureCtx = Context(ctx, definition.symbol)
    signatureCtx.reAppend(
      definition.hp.map(_.symbol) ++
      definition.tp.map(_.symbol) : _*
    )

    val (errs, bounds) = definition.bounds
      .map(setBound(_)(signatureCtx))
      .partitionMap(identity)

    errs match {
      case Vector() =>
        definition.symbol.asClassTypeSymbol.setBound(bounds)
      case errs =>
        errs.foreach(Reporter.appendError)
    }
  }

  def implementInterface(impl: ImplementInterface)(implicit ctx: Context.RootContext): Unit = {
    val signatureCtx = Context(ctx, impl.symbol)
    val implSymbol = impl.symbol.asImplementSymbol

    signatureCtx.reAppend(implSymbol.hps ++ implSymbol.tps: _*)

    val (interfaceErr, interface) = Type.buildType[Symbol.InterfaceSymbol](impl.interface, signatureCtx)
    val (targetErr, target) = Type.buildType[Symbol.ClassTypeSymbol](impl.target, signatureCtx)

    val signatureErr = Vector(interfaceErr, targetErr).flatten
    val (errs, bounds) = impl.bounds
      .map(setBound(_)(signatureCtx))
      .partitionMap(identity)

    (errs ++ signatureErr) match {
      case Vector() =>
        val implContext = Context(signatureCtx, target.tpe.asRefType)
        impl.methods.foreach(Namer.nodeLevelNamed(_, implContext))

        val interfaceTpe = interface.tpe.asRefType
        val targetTpe = target.tpe.asRefType
        val container = ImplementInterfaceContainer(impl, ctx, interfaceTpe, targetTpe, implContext.scope)

        val interfaceSymbol = interface.symbol.asInterfaceSymbol
        impl.symbol.asImplementSymbol.setBound(bounds)
        interfaceSymbol.appendImpl(impl, container)
        SymbolBuffer.append(interfaceSymbol)
      case errs =>
        errs.foreach(Reporter.appendError)
    }
  }

  def implementClass(impl: ImplementClass)(implicit ctx: Context.RootContext): Unit = {
    val signatureCtx = Context(ctx, impl.symbol)
    val implSymbol = impl.symbol.asImplementSymbol
    signatureCtx.reAppend(implSymbol.hps ++ implSymbol.tps: _*)

    val (signatureErr, target) = Type.buildType[Symbol.ClassTypeSymbol](impl.target, signatureCtx)
    val (boundErrs, bounds) = impl.bounds
      .map(setBound(_)(signatureCtx))
      .partitionMap(identity)

    val errs = boundErrs ++ signatureErr.toVector

    errs match {
      case Vector() =>
        val implContext = Context(signatureCtx, target.tpe.asRefType)
        impl.methods.foreach(Namer.nodeLevelNamed(_, implContext))
        impl.stages.foreach(Namer.nodeLevelNamed(_, implContext))

        val container = ImplementClassContainer(impl, ctx, target.tpe.asRefType, implContext.scope)

        val targetSymbol = target.symbol.asClassTypeSymbol
        val implSymbol = impl.symbol.asImplementSymbol
        implSymbol.setBound(bounds)
        targetSymbol.appendImpl(impl, container)
        SymbolBuffer.append(targetSymbol)
      case errs =>
        errs.foreach(Reporter.appendError)
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
    /*
    def verifySameForm(
      tpe0: Type.RefType,
      tpe1: Type.RefType,
      hpBound0: Vector[HPBound],
      hpBound1: Vector[HPBound],
      tpBound0: Vector[TPBound],
      tpBound1: Vector[TPBound]
    ): Option[Type.RefType] = {
      tpe0.isOverlapped(tpe1, hpBound0, hpBound1, tpBound0, tpBound1)

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
     */

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
     * param impl0 impl that has types which are replaced from type parameter into entity type
     * param impl1 impl that has types which are used to replace impl0's type parameter
     * param map   table of (type parameters -> entity type)
     * param tpes  this function used to get all types impl has
     * tparam T    ImplementContainer
     */
      /*
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
     */

    @tailrec
    def verifyClassImplConflict(impls: Vector[ImplementClassContainer]): Unit = {
      def verify(impl0: ImplementClassContainer, impl1: ImplementClassContainer): Either[Error, Unit] = {
        val hasConflict = impl0.targetType.isOverlapped(
          impl1.targetType,
          impl0.symbol.hpBound,
          impl1.symbol.hpBound,
          impl0.symbol.tpBound,
          impl1.symbol.tpBound
        )

        if(hasConflict) Left(Error.ImplementClassConflict(impl0, impl1))
        else Right(())
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
        val hasInterfaceConflict = impl0.targetInterface.isOverlapped(
          impl1.targetInterface,
          impl0.symbol.hpBound,
          impl1.symbol.hpBound,
          impl0.symbol.tpBound,
          impl1.symbol.tpBound
        )

        val hasTargetConflict = impl0.targetType.isOverlapped(
          impl1.targetType,
          impl0.symbol.hpBound,
          impl1.symbol.hpBound,
          impl0.symbol.tpBound,
          impl1.symbol.tpBound
        )

        if(hasInterfaceConflict && hasTargetConflict)
          Left(Error.ImplementInterfaceConflict(impl0, impl1))
        else
          Right(())
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

