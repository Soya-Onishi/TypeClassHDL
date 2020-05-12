package tchdl.typecheck

import tchdl.ast._
import tchdl.util.TchdlException.ImplementationErrorException
import tchdl.util.{Context, Error, HasImpls, Reporter, Scope, Symbol, Type}

import scala.reflect.runtime.universe.{TypeTree => _, _}

object Impler {
  def exec(cu: CompilationUnit) = ???

  def makeRefType(typeTree: TypeAST)(implicit ctx: Context): Either[Error, Type.RefType] = {
    def downcastToTypeSymbol(symbol: Symbol): Either[Error, Symbol.TypeSymbol] =
      symbol match {
        case sym: Symbol.TypeSymbol => Right(sym)
        case sym: Symbol.TermSymbol => Left(Error.SymbolIsTerm(sym.name))
      }

    val result = for {
      tt <- verifyTypeTree(typeTree)
      symbol <- ctx.lookup(tt.name)
      symbol <- downcastToTypeSymbol(symbol)
    } yield (tt, symbol)

    result match {
      case Left(err) => Left(err)
      case Right((tt, symbol)) =>
        val hps = tt.hp
        val tps = tt.tp.map(makeRefType)

        val (errs, typeParams) = tps.partitionMap(a => a)

        if (errs.nonEmpty) Left(Error.MultipleErrors(errs))
        else Right(Type.RefType(symbol, hps, typeParams))
    }
  }

  def implementInterface(impl: ImplementInterface)(implicit ctx: Context.RootContext): Unit = {
    def downcastToInterface(symbol: Symbol): Either[Error, Symbol.InterfaceSymbol] =
      symbol match {
        case sym: Symbol.InterfaceSymbol => Right(sym)
        case sym => Left(Error.RequireInterfaceSymbol(sym.name))
      }

    val implCtx = Context(ctx, impl.symbol)
    impl.hp.foreach(Namer.nodeLevelNamed(_, implCtx))
    impl.tp.foreach(Namer.nodeLevelNamed(_, implCtx))

    val result = for {
      interface <- makeRefType(impl.interface)(implCtx)
      target <- makeRefType(impl.target)(implCtx)
      _ <- downcastToInterface(interface.origin)
      _ <- downcastToStructOrModule(target.origin)
    } yield (interface, target)

    result match {
      case Left(err) => Reporter.appendError(err)
      case Right((interface, target)) =>
        val implCtx = Context(ctx, impl.symbol, target)
        impl.methods.foreach(Namer.nodeLevelNamed(_, implCtx))

        val container = ImplementInterfaceContainer(impl, ctx, interface, target, implCtx.scope)
        interface.origin.asInterfaceSymbol.appendImpl(impl, container)

        SymbolBuffer.append(interface.origin.asInterfaceSymbol)
    }
  }

  def implementClass(impl: ImplementClass)(implicit ctx: Context.RootContext): Unit = {
    val tpe = for {
      target <- makeRefType(impl.target)
      _ <- downcastToStructOrModule(target.origin)
    } yield target

    tpe match {
      case Left(err) => Reporter.appendError(err)
      case Right(tpe) =>
        val implCtx = Context(ctx, impl.symbol, tpe)
        impl.methods.foreach(Namer.nodeLevelNamed(_, implCtx))
        impl.stages.foreach(Namer.nodeLevelNamed(_, implCtx))

        val container = ImplementClassContainer(impl, ctx, tpe, implCtx.scope)

        tpe.origin match {
          case struct: Symbol.StructSymbol =>
            struct.appendImpl(impl, container)
            SymbolBuffer.append(struct)
          case module: Symbol.ModuleSymbol =>
            module.appendImpl(impl, container)
            SymbolBuffer.append(module)
          case symbol =>
            val msg = s"expect struct symbol or module symbol, actual[${symbol.getClass}]"
            throw new ImplementationErrorException(msg)
        }
    }
  }

  def impls(defTree: Definition)(implicit ctx: Context.RootContext): Unit =
    defTree match {
      case impl: ImplementInterface => implementInterface(impl)
      case impl: ImplementClass => implementClass(impl)
      case _ =>
    }

  def downcastToStructOrModule(symbol: Symbol): Either[Error, Symbol.TypeSymbol with HasImpls] =
    symbol match {
      case sym: Symbol.StructSymbol => Right(sym)
      case sym: Symbol.ModuleSymbol => Right(sym)
      case sym => Left(Error.RequireStructOrModuleSymbol(sym.name))
    }

  def verifyTypeTree(tpe: TypeAST): Either[Error, TypeTree] =
    tpe match {
      case t: TypeTree => Right(t)
      case _: SelfType => Left(Error.RejectSelfType)
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
      sets.foreach {
        elem =>
          val invalids = elem.impls.flatMap {
            impl =>
              val beforeCounts = Reporter.errorCounts
              verifier(impl)
              val afterCounts = Reporter.errorCounts

              if(beforeCounts == afterCounts) None
              else Some(impl.id)
          }

          invalids.foreach(elem.removeImpl)
      }

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
        .map{ case (tpe0, tpe1) => (tpe0.replaceWithTypeParamMap(tab), tpe1.replaceWithTypeParamMap(tab)) }
        .flatMap{ case (tpe0, tpe1) => inner(tpe0, tpe1) }

      vec.groupBy(_._1)
        .map{ case (key, pairs) => key -> pairs.head._2 }
        .foreach{ case (key, value) => map(key) = Some(value) }
    }

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
          impl0.targetType.replaceWithTypeParamMap(replaceMap),
          impl1.targetType.replaceWithTypeParamMap(replaceMap)
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
    }

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
            impl0.targetInterface.replaceWithTypeParamMap(replaceMap),
            impl1.targetInterface.replaceWithTypeParamMap(replaceMap)
          )

        val target =
          verifySameForm(
            impl0.targetType.replaceWithTypeParamMap(replaceMap),
            impl1.targetType.replaceWithTypeParamMap(replaceMap)
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

  def isSubject(tpe: Type.RefType): Boolean
  def isValid: Boolean
  def lookup(name: String): Option[Symbol] = scope.lookup(name)
}


abstract class ImplementInterfaceContainer(
  val ctx: Context.RootContext,
  val targetInterface: Type.RefType,
  val targetType: Type.RefType,
  val scope: Scope
) extends ImplementContainer {
  override type TreeType = ImplementInterface

  override def isSubject(tpe: Type.RefType): Boolean = ???

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

  override def isSubject(tpe: Type.RefType): Boolean = ???

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

