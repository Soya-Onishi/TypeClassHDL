package tchdl.util

import tchdl.ast._
import tchdl.typecheck.{Namer, Typer}
import tchdl.util.TchdlException.ImplementationErrorException

import scala.reflect.ClassTag
import scala.reflect.runtime.universe.TypeTag

trait Type {
  def name: String
  def namespace: NameSpace
  def declares: Scope

  def asRefType: Type.RefType = this.asInstanceOf[Type.RefType]
  def asEntityType: Type.EntityType = this.asInstanceOf[Type.EntityType]
  def asParameterType: Type.TypeParamType = this.asInstanceOf[Type.TypeParamType]
  def asMethodType: Type.MethodType = this.asInstanceOf[Type.MethodType]
  def asEnumMemberType: Type.EnumMemberType = this.asInstanceOf[Type.EnumMemberType]

  def isErrorType: Boolean = this.isInstanceOf[Type.ErrorType.type]

  /**
   * This is used for type equality of [[Type.RefType]].
   * [[Type.RefType.hardwareParam]] is [[Expression]], and
   * there is no way to check there is same value
   * if expression uses not only constants but also variables.
   * In [[Type.RefType]], this method verifies [[Type.RefType.origin]] and [[Type.RefType.typeParam]],
   * and does not verify [[Type.RefType.hardwareParam]] because of what explained above.
   */
  def =:=(other: Type): Boolean

  final def =!=(other: Type): Boolean = !(this =:= other)
}

object Type {
  abstract class TypeGenerator extends Type {
    val name = "<?>"

    def declares = throw new TchdlException.ImplementationErrorException("TypeGenerator prohibits an access of 'declares'")
    def namespace = throw new TchdlException.ImplementationErrorException("TypeGenerator prohibits an access of 'namespace'")

    /* ModuleDef and StructDef only need to name its header and components.
         * there is also no need to typed those elements
         * because its process is addressed in another place instead of here
         *
         * If `generate` also do `typed` for each element,
         * it causes cyclic reference for types unexpectedly
         *
         * struct A {
         *   b: Option[B] // cyclic, but legal
         * }
         *
         * struct B {
         *   a: Option[A] // cyclic, but legal
         * }
         *
         * If `generate` do `typed`, in A, refer to type B and
         * B's `generate` also refer to type A.
         * However, A is still TypeGenerator because A's `generate` does not end yet,
       * and it causes cyclic reference error.
       * */
    def generate: Type

    def =:=(other: Type): Boolean =
      throw new ImplementationErrorException("method =:= should not be called in TypeGenerator")
  }

  case class ModuleTypeGenerator(moduleDef: ModuleDef, ctx: Context.RootContext, global: GlobalData) extends TypeGenerator {
    override def generate: Type.EntityType = {
      val sigCtx = Context(ctx, moduleDef.symbol)
      val module = moduleDef.symbol.asEntityTypeSymbol
      sigCtx.reAppend(module.hps ++ module.tps: _*)(global)

      val fieldCtx = Context(sigCtx)

      moduleDef.parents.map(Namer.namedFieldDef(_)(fieldCtx, global))
      moduleDef.siblings.map(Namer.namedFieldDef(_)(fieldCtx, global))

      Type.EntityType(moduleDef.name, ctx.path, fieldCtx.scope)
    }
  }

  case class StructTypeGenerator(struct: StructDef, ctx: Context.RootContext, global: GlobalData) extends TypeGenerator {
    override def generate: Type.EntityType = {
      val sigCtx = Context(ctx, struct.symbol)
      val structSymbol = struct.symbol.asEntityTypeSymbol
      sigCtx.reAppend(structSymbol.hps ++ structSymbol.tps: _*)(global)

      val fieldCtx = Context(sigCtx)
      struct.fields.map(Namer.nodeLevelNamed(_)(fieldCtx, global))
      EntityType(struct.name, ctx.path, fieldCtx.scope)
    }
  }

  case class EnumTypeGenerator(enum: EnumDef, ctx: Context.RootContext, global: GlobalData) extends TypeGenerator {
    override def generate: Type.EntityType = {
      val sigCtx = Context(ctx, enum.symbol)
      val structSymbol = enum.symbol.asEntityTypeSymbol
      sigCtx.reAppend(structSymbol.hps ++ structSymbol.tps: _*)(global)

      val fieldCtx = Context(sigCtx)
      enum.members.map(Namer.nodeLevelNamed(_)(fieldCtx, global))
      EntityType(enum.name, ctx.path, fieldCtx.scope)
    }
  }

  case class InterfaceTypeGenerator(interface: InterfaceDef, ctx: Context.RootContext, global: GlobalData) extends TypeGenerator {
    override def generate: Type = {
      val signatureCtx = Context(ctx, interface.symbol)
      val symbol = interface.symbol.asInterfaceSymbol
      signatureCtx.reAppend(symbol.hps ++ symbol.tps: _*)(global)

      buildThisType(symbol, interface.hp, interface.tp)(signatureCtx, global) match {
        case None => Type.ErrorType
        case Some(thisType) =>
          val bodyCtx = Context(signatureCtx, thisType)

          interface.methods.map(Namer.namedMethod(_)(bodyCtx, global))

          EntityType(interface.name, ctx.path, bodyCtx.scope)
      }
    }
  }

  case class MethodTypeGenerator(methodDef: MethodDef, ctx: Context, global: GlobalData) extends TypeGenerator {
    override def generate: Type = {
      def verifyHPTpes(hps: Vector[ValDef]): Either[Error, Unit] =
        hps.map(_.symbol.tpe).map {
          case Type.ErrorType => Left(Error.DummyError)
          case _ => Right(())
        }.combine(errs => Error.MultipleErrors(errs: _*))

      val signatureCtx = Context(ctx, methodDef.symbol)
      signatureCtx.reAppend(
        methodDef.symbol.asMethodSymbol.hps ++
          methodDef.symbol.asMethodSymbol.tps: _*
      )(global)

      val method = methodDef.symbol.asMethodSymbol
      val hpBoundTrees = methodDef.bounds.collect { case b: HPBoundTree => b }
      val tpBoundTrees = methodDef.bounds.collect { case b: TPBoundTree => b }

      val result = for {
        _ <- verifyHPTpes(methodDef.hp)
        _ <- HPBound.verifyAllForms(hpBoundTrees)(signatureCtx, global)
        hpBounds = hpBoundTrees.map(HPBound.apply)
        (targetErrs, targets) = tpBoundTrees.view.map(_.target).map(TPBound.buildTarget(_)(signatureCtx, global)).toVector.unzip
        (boundsErrs, bounds) = tpBoundTrees.view.map(_.bounds).map(TPBound.buildBounds(_)(signatureCtx, global)).toVector.unzip
        errs = (targetErrs ++ boundsErrs).flatten
        _ <- if (errs.nonEmpty) Left(Error.MultipleErrors(errs: _*)) else Right(())
        tpBounds = (targets zip bounds).view
          .map { case (t, bs) => (t.tpe.asRefType, bs.map(_.tpe.asRefType)) }
          .map { case (t, bs) => TPBound(t, bs) }
          .toVector
        _ = method.setBound(hpBounds ++ tpBounds)
        paramSymbols = methodDef.params
          .map(Namer.nodeLevelNamed(_)(signatureCtx, global))
          .map(Typer.typedValDef(_)(signatureCtx, global))
          .map(_.symbol)
        retTpeTree = Typer.typedTypeTree(methodDef.retTpe)(signatureCtx, global)
        _ = methodDef.retTpe.setSymbol(retTpeTree.symbol).setTpe(retTpeTree.tpe)
        tpes = paramSymbols.map(_.tpe) :+ retTpeTree.tpe
        _ <- if (tpes.exists(_.isErrorType)) Left(Error.DummyError) else Right(())
      } yield (paramSymbols.map(_.tpe.asRefType), retTpeTree.tpe.asRefType)

      result match {
        case Right((params, ret)) => MethodType(params, ret)
        case Left(err) =>
          global.repo.error.append(err)
          Type.ErrorType
      }
    }
  }

  case class VariableTypeGenerator(vdef: ValDef, ctx: Context.NodeContext, global: GlobalData) extends TypeGenerator {
    override def generate: Type = {
      val ValDef(_, _, tpeTree, expr) = vdef

      (tpeTree, expr) match {
        case (None, None) =>
          global.repo.error.append(Error.RequireTypeTree)
          Type.ErrorType
        case (None, Some(expr)) =>
          val typedExpr = Typer.typedExpr(expr)(ctx, global)
          global.cache.set(typedExpr)
          typedExpr.tpe
        case (Some(tpe), _) =>
          val typedTpe = Typer.typedTypeTree(tpe)(ctx, global)
          global.cache.set(typedTpe)
          typedTpe.tpe
      }
    }
  }

  case class EnumMemberTypeGenerator(member: EnumMemberDef, ctx: Context.NodeContext, global: GlobalData) extends TypeGenerator {
    override def generate: Type = {
      val name = member.name

      val scope = new Scope
      val fields = member.fields.map(Typer.typedTypeTree(_)(ctx, global))
      val symbols = fields.zipWithIndex.map {
        case (field, idx) =>
          Symbol.VariableSymbol.field(
            name = s"_$idx",
            ctx.path.appendComponentName(member.name),
            Accessibility.Private,
            Modifier.Field,
            field.tpe
          )
      }

      symbols.foreach(scope.append)

      val hasError = fields.exists(_.tpe.isErrorType)
      val parent = ctx.owner.tpe.asEntityType

      if (hasError) Type.ErrorType
      else EnumMemberType(name, ctx.path, parent, scope)
    }
  }

  case class HPTypeGenerator(vdef: ValDef, ctx: Context.NodeContext, global: GlobalData) extends TypeGenerator {
    override def generate: Type = {
      val ValDef(_, _, Some(typeTree), _) = vdef

      implicit val tpeCtx: Context.NodeContext = ctx
      implicit val tpeGlobal: GlobalData = global
      val (err, ttree) = Type.buildType[Symbol.ClassTypeSymbol](typeTree)
      global.cache.set(ttree)

      err match {
        case Some(err) =>
          global.repo.error.append(err)
          Type.ErrorType
        case None =>
          val tpe = ttree.tpe.asRefType
          val pkgName = tpe.origin.path.pkgName
          val name = tpe.origin.name

          pkgName :+ name match {
            case Vector("std", "types", "Num") => tpe
            case Vector("std", "types", "Str") => tpe
            case _ =>
              global.repo.error.append(Error.RequireSpecificType(tpe, Type.numTpe, Type.strTpe))
              Type.ErrorType
          }
      }
    }
  }

  case class StageTypeGenerator(stage: StageDef, ctx: Context.NodeContext, global: GlobalData) extends TypeGenerator {
    override def generate: Type.MethodType = {
      val paramCtx = Context(ctx, stage.symbol)
      val typedParams = stage.params
        .map(Namer.nodeLevelNamed(_)(paramCtx, global))
        .map(Typer.typedValDef(_)(paramCtx, global))
        .map(_.symbol.tpe.asRefType)

      val typedTpe = Typer.typedTypeTree(stage.retTpe)(paramCtx, global)

      MethodType(typedParams, typedTpe.tpe.asRefType)
    }
  }

  abstract class DeclaredType extends Type {
    def returnType: Type = this
  }

  class EntityType(
    val name: String,
    val namespace: NameSpace,
    val declares: Scope
  ) extends DeclaredType {
    override def =:=(other: Type): Boolean = other match {
      case other: EntityType =>
        this.name == this.name && this.namespace == other.namespace
      case _ => false
    }
  }

  object EntityType {
    def apply(
      name: String,
      namespace: NameSpace,
      declares: Scope
    ): EntityType =
      new EntityType(name, namespace, declares)
  }

  class TypeParamType(
    val name: String,
    val namespace: NameSpace,
  ) extends DeclaredType {
    val declares: Scope = Scope.empty

    private var constraints: Vector[Type.RefType] = null

    def appendConstraints(constraints: Vector[Type.RefType]): Unit = {
      if (this.constraints == null)
        this.constraints = constraints
      else
        throw new ImplementationErrorException("constraints is already assigned")
    }

    def getConstraints: Vector[Type.RefType] = {
      if (this.constraints == null)
        throw new ImplementationErrorException("constraints is not assigned yet")
      else
        this.constraints
    }

    override def =:=(other: Type): Boolean = other match {
      case other: TypeParamType => this.name == other.name && this.namespace == other.namespace
    }
  }

  object TypeParamType {
    def apply(name: String, namespace: NameSpace): TypeParamType =
      new TypeParamType(name, namespace)
  }

  class MethodType(
    val params: Vector[Type.RefType],
    val returnType: Type.RefType
  ) extends Type {
    lazy val name: String = {
      val argTypeNames = params.map(_.name).mkString(", ")
      s"($argTypeNames) -> ${returnType.name}"
    }

    val namespace: NameSpace = NameSpace.empty
    val declares: Scope = returnType.declares

    def replaceWithMap(hpMap: Map[Symbol.HardwareParamSymbol, HPExpr], tpMap: Map[Symbol.TypeParamSymbol, Type.RefType]): Type.MethodType = {
      def replace: PartialFunction[Type, Type.RefType] = {
        case tpe: Type.RefType => tpe.replaceWithMap(hpMap, tpMap)
      }

      val replacedArgs = params.collect(replace)
      val replacedRetTpe = Some(returnType).collect(replace).get

      MethodType(replacedArgs, replacedRetTpe)
    }

    override def equals(obj: Any): Boolean = obj match {
      case that: MethodType =>
        def isSameParam: Boolean = this.params == that.params
        def isSameRet: Boolean = this.returnType == that.returnType

        isSameParam && isSameRet
    }

    def =:=(that: Type): Boolean = this == that
  }

  object MethodType {
    def apply(args: Vector[Type.RefType], retTpe: RefType): MethodType = new MethodType(args, retTpe)
  }

  class EnumMemberType(
    val name: String,
    val namespace: NameSpace,
    val parent: EntityType,
    val declares: Scope = Scope.empty
  ) extends Type {
    override def =:=(tpe: Type): Boolean = tpe match {
      case that: EnumMemberType => this.name == that.name && this.namespace == that.namespace
      case _ => false
    }

    def fields: Vector[Symbol] = declares
      .toMap.toVector
      .sortWith{ case ((left, _), (right, _)) => left < right }
      .map{ case (_, symbol) => symbol }
  }

  object EnumMemberType {
    def apply(name: String, namespace: NameSpace, parent: EntityType, declares: Scope): EnumMemberType = {
      new EnumMemberType(name, namespace, parent, declares)
    }
  }

  class RefType(
    val origin: Symbol.TypeSymbol,
    val hardwareParam: Vector[HPExpr],
    val typeParam: Vector[Type.RefType],
  ) extends Type {
    val name: String = origin.name
    val namespace: NameSpace = origin.path

    override def declares: Scope = origin.tpe.declares

    def lookupField(name: String, callerHPBounds: Vector[HPBound], callerTPBounds: Vector[TPBound])(implicit global: GlobalData): LookupResult[Symbol.TermSymbol] = {
      def lookupToClass: LookupResult[Symbol.TermSymbol] =
        origin.tpe.declares.lookup(name) match {
          // TODO: verify whether this logic needs to replace type parameter into actual type or not
          case Some(symbol: Symbol.TermSymbol) => LookupResult.LookupSuccess(symbol)
          case Some(symbol) => LookupResult.LookupFailure(Error.RequireSymbol[Symbol.TermSymbol](symbol))
          case None => LookupResult.LookupFailure(Error.SymbolNotFound(name))
        }

      def verifyEachBounds(hpBounds: Vector[HPBound], tpBounds: Vector[TPBound]): Either[Error, Unit] = {
        val (hpErrs, _) = hpBounds
          .map(HPBound.verifyMeetBound(_, callerHPBounds))
          .partitionMap(identity)

        val (tpErrs, _) = tpBounds
          .map(TPBound.verifyMeetBound(_, callerHPBounds, callerTPBounds))
          .partitionMap(identity)

        val errs = hpErrs ++ tpErrs
        if (errs.isEmpty) Right(())
        else Left(Error.SymbolNotFound(name))
      }

      def lookupFromImpl(clazz: Symbol.ClassTypeSymbol): LookupResult[Symbol.TermSymbol] = {
        val result = clazz.impls.foldLeft[Either[Error, Symbol.TermSymbol]](Left(Error.DummyError)) {
          case (right @ Right(_), _) => right
          case (Left(_), impl) =>
            val implSymbol = impl.symbol.asImplementSymbol
            val (initHPTable, initTPTable) = RefType.buildTable(impl)
            val result = for {
              hpTable <- RefType.assignHPTable(initHPTable, Vector(this), Vector(impl.targetType))
              tpTable <- RefType.assignTPTable(initTPTable, Vector(this), Vector(impl.targetType))
              swappedHPBounds = HPBound.swapBounds(implSymbol.hpBound, hpTable)
              swappedTPBounds = TPBound.swapBounds(implSymbol.tpBound, hpTable, tpTable)
              simplifiedHPBounds <- HPBound.simplify(swappedHPBounds)
              _ <- verifyEachBounds(simplifiedHPBounds, swappedTPBounds)
            } yield impl

            result.flatMap(
              _.lookup[Symbol.VariableSymbol](name)
                .map(Right.apply)
                .getOrElse(Left(Error.SymbolNotFound(name)))
            )
        }

        result match {
          case Left(err) => LookupResult.LookupFailure(err)
          case Right(symbol) => LookupResult.LookupSuccess(symbol)
        }
      }

      this.origin match {
        case clazz: Symbol.ClassTypeSymbol => lookupToClass match {
          case success @ LookupResult.LookupSuccess(_) => success
          case LookupResult.LookupFailure(_) => lookupFromImpl(clazz)
        }
        case symbol => LookupResult.LookupFailure(Error.RequireSymbol[Symbol.ClassTypeSymbol](symbol))
      }
    }

    def lookupMethod(
      methodName: String,
      callerHP: Vector[HPExpr],
      callerTP: Vector[Type.RefType],
      args: Vector[Type.RefType],
      callerHPBound: Vector[HPBound],
      callerTPBound: Vector[TPBound],
      requireStatic: Boolean
    )(implicit ctx: Context.NodeContext, globalData: GlobalData): LookupResult[(Symbol.MethodSymbol, Type.MethodType)] = {
      val result = this.origin match {
        case entity: Symbol.EntityTypeSymbol =>
          lookupFromImpls(
            entity.impls,
            methodName,
            args,
            callerHP,
            callerTP,
            callerHPBound,
            callerTPBound,
            requireStatic
          ) match {
            case success @ Right(_) => success
            case Left(_) if ctx.interfaceTable.isEmpty => Left(Error.SymbolNotFound(methodName))
            case Left(_) =>
              val (errs, methods) = ctx.interfaceTable
                .values.view
                .map(_.impls)
                .map(lookupFromImpls(_, methodName, args, callerHP, callerTP, callerHPBound, callerTPBound, requireStatic))
                .toVector
                .partitionMap(identity)

              methods match {
                case Vector() => Left(Error.MultipleErrors(errs: _*))
                case Vector(method) => Right(method)
                case methods => Left(Error.AmbiguousSymbols(methods.map(_._1)))
              }
          }
        case tp: Symbol.TypeParamSymbol =>
          callerTPBound.find(_.target.origin == tp) match {
            case None => Left(Error.SymbolNotFound(methodName))
            case Some(bound) =>
              bound.bounds.foldLeft[Either[Error, (Symbol.MethodSymbol, Type.MethodType)]](Left(Error.DummyError)) {
                case (success @ Right(_), _) => success
                case (Left(errs), interface) =>
                  val result = lookupFromTypeParam(
                    interface.origin.asInterfaceSymbol,
                    interface.hardwareParam,
                    interface.typeParam,
                    methodName,
                    args,
                    callerHP,
                    callerTP,
                    callerHPBound,
                    callerTPBound,
                    requireStatic
                  )

                  result match {
                    case Left(err) => Left(Error.MultipleErrors(err, errs))
                    case success @ Right(_) => success
                  }
              }
          }
      }

      result match {
        case Left(err) => LookupResult.LookupFailure(err)
        case Right(pair) => LookupResult.LookupSuccess(pair)
      }
    }

    def lookupFromEntity[T <: ImplementContainer](
      impl: T,
      methodName: String,
      target: Type.RefType,
      args: Vector[Type.RefType],
      callerHP: Vector[HPExpr],
      callerTP: Vector[Type.RefType],
      callerHPBound: Vector[HPBound],
      callerTPBound: Vector[TPBound]
    )(implicit global: GlobalData): Either[Error, (Symbol.MethodSymbol, Type.MethodType)] = {
      val (initHpTable, initTpTable) = RefType.buildTable(impl)
      val lookupResult = impl.lookup[Symbol.MethodSymbol](methodName) match {
        case None => Left(Error.SymbolNotFound(methodName))
        case Some(symbol) => Right(symbol)
      }

      for {
        method <- lookupResult
        _ <- RefType.verifySignatureLength(method, args, callerHP, callerTP)
        methodTpe = method.tpe.asMethodType
        callers = target +: args
        targets = impl.targetType +: methodTpe.params
        _ <- RefType.verifySuperSets(callers, targets)
        hpTable <- RefType.assignHPTable(initHpTable, callers, targets)
        tpTable <- RefType.assignTPTable(initTpTable, callers, targets)
        swappedHpBound = HPBound.swapBounds(impl.symbol.hpBound, hpTable)
        swappedTpBound = TPBound.swapBounds(impl.symbol.tpBound, hpTable, tpTable)
        simplifiedHPBound <- HPBound.simplify(swappedHpBound)
        _ <- Bound.verifyEachBounds(simplifiedHPBound, swappedTpBound, callerHPBound, callerTPBound, impl, target)
        (methodHpTable, methodTpTable) = RefType.buildSymbolTable(method, callerHP, callerTP)
        appendHpTable = hpTable ++ methodHpTable
        appendTpTable = tpTable ++ methodTpTable
        methodHpBound = HPBound.swapBounds(method.hpBound, appendHpTable)
        methodTpBound = TPBound.swapBounds(method.tpBound, appendHpTable, appendTpTable)
        _ <- Bound.verifyEachBounds(methodHpBound, methodTpBound, callerHPBound, callerTPBound, impl, target)
        swappedTpe = RefType.assignMethodTpe(methodTpe, appendHpTable, appendTpTable)
        _ <- RefType.verifyMethodType(swappedTpe, args)
      } yield (method, swappedTpe)
    }

    def lookupFromTypeParam(
      interface: Symbol.InterfaceSymbol,
      interfaceHPs: Vector[HPExpr],
      interfaceTPs: Vector[Type.RefType],
      methodName: String,
      args: Vector[Type.RefType],
      callerHP: Vector[HPExpr],
      callerTP: Vector[Type.RefType],
      callerHPBound: Vector[HPBound],
      callerTPBound: Vector[TPBound],
      requireStatic: Boolean
    )(implicit global: GlobalData): Either[Error, (Symbol.MethodSymbol, Type.MethodType)] = {
      val (initHpTable, initTpTable) = RefType.buildSymbolTable(interface, interfaceHPs, interfaceTPs)
      val lookupResult: Either[Error, Symbol.MethodSymbol] = interface.tpe.declares.lookup(methodName) match {
        case Some(symbol: Symbol.MethodSymbol) if requireStatic && symbol.hasFlag(Modifier.Static)=> Right(symbol)
        case Some(symbol: Symbol.MethodSymbol) if symbol.hasFlag(Modifier.Static) => Left(Error.ReferMethodAsNormal(symbol))
        case Some(symbol: Symbol.MethodSymbol) if requireStatic => Left(Error.ReferMethodAsStatic(symbol))
        case Some(symbol: Symbol.MethodSymbol) => Right(symbol)
        case Some(_) => Left(Error.SymbolNotFound(methodName))
        case None => Left(Error.SymbolNotFound(methodName))
      }

      def verifyEachBounds(hpBounds: Vector[HPBound], tpBounds: Vector[TPBound]): Either[Error, Unit] = {
        val (hpErrs, _) = hpBounds
          .map(HPBound.verifyMeetBound(_, callerHPBound))
          .partitionMap(identity)

        val (tpErrs, _) = tpBounds
          .map(TPBound.verifyMeetBound(_, callerHPBound, callerTPBound))
          .partitionMap(identity)

        val errs = hpErrs ++ tpErrs
        if (errs.isEmpty) Right(())
        else Left(Error.MultipleErrors(errs: _*))
      }

      for {
        method <- lookupResult
        (methodHpTable, methodTpTable) = RefType.buildSymbolTable(method, callerHP, callerTP)
        hpTable = initHpTable ++ methodHpTable
        tpTable = initTpTable ++ methodTpTable
        swappedHPBounds = HPBound.swapBounds(method.hpBound, hpTable)
        swappedTPBounds = TPBound.swapBounds(method.tpBound, hpTable, tpTable)
        simplifiedHPBounds <- HPBound.simplify(swappedHPBounds)
        _ <- verifyEachBounds(simplifiedHPBounds, swappedTPBounds)
        methodTpe = method.tpe.asMethodType
        swappedTpe = RefType.assignMethodTpe(methodTpe, hpTable, tpTable)
        _ <- RefType.verifyMethodType(swappedTpe, args)
      } yield (method, swappedTpe)
    }

    def lookupFromImpls(
      impls: Iterable[ImplementContainer],
      methodName: String,
      args: Vector[Type.RefType],
      callerHP: Vector[HPExpr],
      callerTP: Vector[Type.RefType],
      callerHPBound: Vector[HPBound],
      callerTPBound: Vector[TPBound],
      requireStatic: Boolean
    )(implicit global: GlobalData): Either[Error, (Symbol.MethodSymbol, Type.MethodType)] = {
      val result = impls.foldLeft[Either[Error, (Symbol.MethodSymbol, Type.MethodType)]](Left(Error.DummyError)) {
        case (right @ Right(_), _) => right
        case (Left(errs), impl) =>
          lookupFromEntity(
            impl,
            methodName,
            this,
            args,
            callerHP,
            callerTP,
            callerHPBound,
            callerTPBound
          ) match {
            case Right((symbol, tpe)) if requireStatic && symbol.hasFlag(Modifier.Static)=> Right(symbol, tpe)
            case Right((symbol, _)) if requireStatic => Left(Error.ReferMethodAsStatic(symbol))
            case Right((symbol, _)) if symbol.hasFlag(Modifier.Static) => Left(Error.ReferMethodAsNormal(symbol))
            case Right((symbol, tpe)) => Right(symbol, tpe)
            case Left(err) => Left(Error.MultipleErrors(err, errs))
          }
      }

      result match {
        case right @ Right(_) => right
        case Left(Error.DummyError) => Left(Error.SymbolNotFound(methodName))
        case other @ Left(_) => other
      }
    }

    def lookupStage(
      stageName: String,
      args: Vector[Type.RefType],
      callerHPBounds: Vector[HPBound],
      callerTPBounds: Vector[TPBound]
    )(implicit global: GlobalData): LookupResult[(Symbol.StageSymbol, Type.MethodType)] = {
      def verifySignatureLength(stage: Symbol.StageSymbol): Either[Error, Unit] = {
        val paramLength = stage.tpe.asMethodType.params.length
        val argLength = args.length

        if (paramLength == argLength) Right(())
        else Left(Error.ParameterLengthMismatch(paramLength, argLength))
      }

      def lookupFromImpl(impl: ImplementContainer): Either[Error, (Symbol.StageSymbol, Type.MethodType)] = {
        val (initHPTable, initTPTable) = RefType.buildTable(impl)
        val lookupResult = impl.lookup[Symbol.StageSymbol](stageName) match {
          case None => Left(Error.SymbolNotFound(stageName))
          case Some(symbol) => Right(symbol)
        }

        for {
          stage <- lookupResult
          _ <- verifySignatureLength(stage)
          stageTpe = stage.tpe.asMethodType
          callers = this +: args
          targets = impl.targetType +: stageTpe.params
          _ <- RefType.verifySuperSets(callers, targets)
          hpTable <- RefType.assignHPTable(initHPTable, callers, targets)
          tpTable <- RefType.assignTPTable(initTPTable, callers, targets)
          swappedHpBound = HPBound.swapBounds(impl.symbol.hpBound, hpTable)
          swappedTpBound = TPBound.swapBounds(impl.symbol.tpBound, hpTable, tpTable)
          simplifiedHPBound <- HPBound.simplify(swappedHpBound)
          _ <- Bound.verifyEachBounds(simplifiedHPBound, swappedTpBound, Vector.empty, Vector.empty, impl, this)
          swappedTpe = RefType.assignMethodTpe(stageTpe, hpTable, tpTable)
          _ <- RefType.verifyMethodType(swappedTpe, args)
        } yield (stage, stageTpe)
      }

      val impls = this.origin.asInstanceOf[Symbol.EntityTypeSymbol].impls
      val result = impls.foldLeft[Either[Error, (Symbol.StageSymbol, Type.MethodType)]](Left(Error.DummyError)) {
        case (right @ Right(_), _) => right
        case (Left(errs), impl) => lookupFromImpl(impl) match {
          case right @ Right(_) => right
          case Left(err) => Left(Error.MultipleErrors(errs, err))
        }
      }

      result match {
        case Right(pair) => LookupResult.LookupSuccess(pair)
        case Left(err) => LookupResult.LookupFailure(err)
      }
    }

    def lookupOperator(
      op: Operation,
      arg: Type.RefType,
      callerHPBounds: Vector[HPBound],
      callerTPBounds: Vector[TPBound]
    )(implicit global: GlobalData): LookupResult[(Symbol.MethodSymbol, Type.MethodType)] = {
      val interface = global.builtin.interfaces.lookup(op.toInterface)
      this.origin match {
        case _: Symbol.EntityTypeSymbol =>
          val (errs, methods) = interface.impls
            .map(impl => lookupFromEntity(
              impl,
              op.toMethod,
              this,
              Vector(arg),
              Vector.empty,
              Vector.empty,
              callerHPBounds,
              callerTPBounds
            ))
            .partitionMap(identity)

          methods match {
            case Vector() => errs match {
              case Vector() => LookupResult.LookupFailure(Error.OperationNotFound(op))
              case errs => LookupResult.LookupFailure(Error.MultipleErrors(errs: _*))
            }
            case Vector(method) => LookupResult.LookupSuccess(method)
            case methods => LookupResult.LookupFailure(Error.AmbiguousSymbols(methods.map(_._1)))
          }
        case _: Symbol.TypeParamSymbol =>
          callerTPBounds.find(_.target =:= this) match {
            case None => LookupResult.LookupFailure(Error.OperationNotFound(op))
            case Some(tpBound) => tpBound.bounds.find(_.origin == interface) match {
              case None => LookupResult.LookupFailure(Error.OperationNotFound(op))
              case Some(interfaceTpe) =>
                val result = lookupFromTypeParam(
                  interface,
                  interfaceTpe.hardwareParam,
                  interfaceTpe.typeParam,
                  op.toMethod,
                  Vector(arg),
                  Vector.empty,
                  Vector.empty,
                  callerHPBounds,
                  callerTPBounds,
                  requireStatic = false
                )

                result match {
                  case Left(err) => LookupResult.LookupFailure(err)
                  case Right(pair) => LookupResult.LookupSuccess(pair)
                }
            }
          }
      }
    }

    def lookupMethodFromBounds(
      args: Vector[Type.RefType],
      callerHP: Vector[HPExpr],
      callerTP: Vector[Type.RefType],
      bounds: Vector[Type.RefType],
      methodName: String,
      requireStatic: Boolean
    )(implicit global: GlobalData): (Symbol.MethodSymbol, Type.MethodType) = {
      val impls = bounds.view
        .map(_.origin.asInterfaceSymbol)
        .flatMap(_.impls)

      val lookupResult = lookupFromImpls(
        impls,
        methodName,
        args,
        callerHP,
        callerTP,
        Vector.empty,
        Vector.empty,
        requireStatic
      )

      lookupResult.getOrElse(throw new ImplementationErrorException("method should be found"))
    }

    // TODO: lookup type that is defined at implementation
    def lookupType[T <: Symbol.TypeSymbol : ClassTag : TypeTag](name: String): LookupResult[T] = {
      def lookupFromEnum(symbol: Symbol.EnumSymbol): LookupResult[T] = {
        symbol.tpe.declares.lookup(name) match {
          case None => LookupResult.LookupFailure(Error.SymbolNotFound(name))
          case Some(symbol: T) => LookupResult.LookupSuccess(symbol)
          case Some(symbol) => LookupResult.LookupFailure(Error.RequireSymbol[Symbol.TypeSymbol](symbol))
        }
      }

      this.origin match {
        case symbol: Symbol.EnumSymbol => lookupFromEnum(symbol)
        case _ => throw new ImplementationErrorException("reference to field type except for enum does not support yet.")
      }
    }

    def replaceWithMap(hpTable: Map[Symbol.HardwareParamSymbol, HPExpr], tpTable: Map[Symbol.TypeParamSymbol, Type.RefType]): Type.RefType =
      origin match {
        case symbol: Symbol.TypeParamSymbol => tpTable.getOrElse(symbol, this)
        case _ => RefType(
          this.origin,
          this.hardwareParam.map(_.replaceWithMap(hpTable)),
          typeParam.map(_.replaceWithMap(hpTable, tpTable))
        )
      }

    override def equals(obj: Any): Boolean = obj match {
      case that: Type.RefType =>
        def isSameOrigin = this.origin == that.origin

        def isSameHp = {
          def isSameLength = this.hardwareParam.length == that.hardwareParam.length

          def isSameExpr = this.hardwareParam
            .zip(that.hardwareParam)
            .forall { case (t, o) => t.isSameExpr(o) }

          isSameLength && isSameExpr
        }

        def isSameTP = {
          def isSameLength = this.typeParam.length == that.typeParam.length

          def isSameTypes = (this.typeParam zip that.typeParam).forall { case (t, o) => t =:= o }

          isSameLength && isSameTypes
        }

        isSameOrigin && isSameHp && isSameTP
      case _ => false
    }

    override def =:=(other: Type): Boolean = other match {
      case that: RefType => this == that
      case _ => false
    }

    def isModuleType(implicit ctx: Context.NodeContext, global: GlobalData): Boolean = this.origin match {
      case _: Symbol.ModuleSymbol => true
      case _: Symbol.InterfaceSymbol => false
      case tp: Symbol.TypeParamSymbol => ctx.tpBounds.find(_.target.origin == tp) match {
        case None => false
        case Some(tpBound) =>
          val moduleInterface = Type.RefType(global.builtin.interfaces.lookup("Module"))
          tpBound.bounds.exists(_ =:= moduleInterface)
      }
    }

    def isHardwareType(implicit ctx: Context, global: GlobalData): Boolean = {
      val builtinSymbols = global.builtin.types.symbols

      def loop(verified: Type.RefType, types: Set[Type.RefType]): Boolean = {
        def verify: Boolean = verified.origin match {
          case _: Symbol.ModuleSymbol => false
          case _: Symbol.InterfaceSymbol => false
          case tp: Symbol.TypeParamSymbol => ctx.tpBounds.find(_.target.origin == tp) match {
            case None => false
            case Some(tpBound) =>
              val hardwareInterface = Type.RefType(global.builtin.interfaces.lookup("HW"))
              tpBound.bounds.exists(_ =:= hardwareInterface)
          }
          case struct: Symbol.StructSymbol if struct == Symbol.bit  => true
          case struct: Symbol.StructSymbol if struct == Symbol.int  => true
          case struct: Symbol.StructSymbol if struct == Symbol.bool => true
          case struct: Symbol.StructSymbol if struct == Symbol.unit => true
          case struct: Symbol.StructSymbol if builtinSymbols.contains(struct) => false
          case struct: Symbol.StructSymbol if struct.tpe.declares.toMap.isEmpty => false
          case struct: Symbol.StructSymbol =>
            val hpTable = (struct.hps zip verified.hardwareParam).toMap
            val tpTable = (struct.tps zip verified.typeParam).toMap
            val fields = struct.tpe.declares.toMap.values.toVector
            val fieldTpes = fields.map(_.tpe.asRefType.replaceWithMap(hpTable, tpTable))
            fieldTpes.forall(loop(_, types + verified))
          case enum: Symbol.EnumSymbol =>
            val hpTable = (enum.hps zip verified.hardwareParam).toMap
            val tpTable = (enum.tps zip verified.typeParam).toMap
            val memberFieldTpes = enum.tpe.declares.toMap
              .values
              .toVector
              .map(_.tpe.asEnumMemberType)
              .flatMap(_.declares.toMap.values)
              .map(_.tpe.asRefType)
              .map(_.replaceWithMap(hpTable, tpTable))

            memberFieldTpes.forall(loop(_, types + verified))
        }

        if (types(verified)) false
        else verify
      }

      loop(this, Set.empty)
    }

    override def toString: String = {
      val name = this.origin.name
      val hps = this.hardwareParam.map(_.toString).mkString(", ")
      val tps = this.typeParam.map(_.toString).mkString(", ")
      val params =
        if (this.typeParam.isEmpty && this.hardwareParam.isEmpty) ""
        else if (this.hardwareParam.isEmpty) s"[$tps]"
        else if (this.typeParam.isEmpty) s"[$hps]"
        else s"[$hps, $tps]"

      s"$name$params"
    }
  }

  object RefType {
    def apply(origin: Symbol.TypeSymbol, hp: Vector[HPExpr], tp: Vector[Type.RefType]): Type.RefType =
      new RefType(origin, hp, tp)

    def apply(origin: Symbol.TypeSymbol): RefType =
      new RefType(origin, Vector.empty, Vector.empty)

    def unapply(obj: Any): Option[(Symbol.TypeSymbol, Vector[HPExpr], Vector[RefType])] = obj match {
      case tpe: Type.RefType => Some((tpe.origin, tpe.hardwareParam, tpe.typeParam))
      case _ => None
    }

    def buildTable(impl: ImplementContainer): (Map[Symbol.HardwareParamSymbol, Option[HPExpr]], Map[Symbol.TypeParamSymbol, Option[Type.RefType]]) = {
      val hpTable = impl.hardwareParam.map(_ -> Option.empty[HPExpr]).toMap
      val tpTable = impl.typeParam.map(_ -> Option.empty[Type.RefType]).toMap

      (hpTable, tpTable)
    }

    def buildSymbolTable(symbol: Symbol with HasParams, hps: Vector[HPExpr], tps: Vector[Type.RefType]): (Map[Symbol.HardwareParamSymbol, HPExpr], Map[Symbol.TypeParamSymbol, Type.RefType]) = {
      val hpTable = (symbol.hps zip hps).toMap
      val tpTable = (symbol.tps zip tps).toMap

      (hpTable, tpTable)
    }

    def verifySignatureLength(
      method: Symbol.MethodSymbol,
      args: Vector[Type.RefType],
      callerHP: Vector[HPExpr],
      callerTP: Vector[Type.RefType]
    ): Either[Error, Unit] = {
      val params = method.tpe.asMethodType.params
      val hps = method.hps
      val tps = method.tps

      lazy val paramMissMatch = Error.ParameterLengthMismatch(params.length, args.length)
      lazy val hpsMissMatch = Error.HardParameterLengthMismatch(hps.length, callerHP.length)
      lazy val tpsMissMatch = Error.TypeParameterLengthMismatch(tps.length, callerTP.length)

      if (params.length != args.length) Left(paramMissMatch)
      else if (hps.length != callerHP.length) Left(hpsMissMatch)
      else if (tps.length != callerTP.length) Left(tpsMissMatch)
      else Right(())
    }

    def verifySuperSets(
      caller: Vector[Type.RefType],
      target: Vector[Type.RefType]
    ): Either[Error, Unit] = {
      def isHpSuperSet(caller: HPExpr, target: HPExpr): Boolean =
        (caller, target) match {
          case (_: Ident, _: IntLiteral) => false
          case (_: HPBinOp, _: IntLiteral) => false
          case (_: Ident, _: StringLiteral) => false
          case (_: HPBinOp, _: StringLiteral) => false
          case _ => true
        }

      def verify(caller: Type.RefType, target: Type.RefType): Either[Error, Unit] = {
        (caller.origin, target.origin) match {
          case (e0: Symbol.EntityTypeSymbol, e1: Symbol.EntityTypeSymbol) =>
            if (e0 != e1) Left(Error.TypeMismatch(target, caller))
            else {
              val validHPs = caller.hardwareParam
                .zip(target.hardwareParam)
                .forall { case (c, t) => isHpSuperSet(c, t) }

              val validTPs = caller.typeParam
                .zip(target.typeParam)
                .map { case (c, t) => verify(c, t) }
                .forall(_.isRight)

              if (validHPs && validTPs) Right(())
              else Left(Error.TypeMismatch(target, caller))
            }
          case (_, _: Symbol.TypeParamSymbol) => Right(())
          case (_: Symbol.TypeParamSymbol, _) => Left(Error.TypeMismatch(target, caller))
        }
      }

      val (errs, _) = (caller zip target)
        .map { case (c, t) => verify(c, t) }
        .partitionMap(identity)

      if (errs.isEmpty) Right(())
      else Left(Error.MultipleErrors(errs: _*))
    }

    def unwrapTable[K, V](table: Map[K, Option[V]])(err: K => Error): Either[Error, Map[K, V]] = {
      val (errs, pairs) = table.map {
        case (key, Some(value)) => Right(key -> value)
        case (key, None) => Left(err(key))
      }.partitionMap(identity)

      if (errs.isEmpty) Right(pairs.toMap)
      else Left(Error.MultipleErrors(errs.toSeq: _*))
    }


    def assignHPTable(
      table: Map[Symbol.HardwareParamSymbol, Option[HPExpr]],
      caller: Vector[Type.RefType],
      targets: Vector[Type.RefType]
    ): Either[Error, Map[Symbol.HardwareParamSymbol, HPExpr]] = {
      def assign(
        caller: HPExpr,
        target: HPExpr,
        table: Map[Symbol.HardwareParamSymbol, Option[HPExpr]]
      ): Map[Symbol.HardwareParamSymbol, Option[HPExpr]] =
        (caller, target) match {
          case (expr, ident: Ident) =>
            val hp = ident.symbol.asHardwareParamSymbol
            table.get(hp) match {
              case Some(None) => table.updated(hp, Some(expr))
              case Some(Some(_)) => table
              case None => throw new ImplementationErrorException(s"${hp.name} should be as key")
            }
          case _ => table
        }


      def update(
        caller: Type.RefType,
        target: Type.RefType,
        table: Map[Symbol.HardwareParamSymbol, Option[HPExpr]]
      ): Map[Symbol.HardwareParamSymbol, Option[HPExpr]] = {
        (caller.origin, target.origin) match {
          case (_: Symbol.EntityTypeSymbol, _: Symbol.EntityTypeSymbol) =>
            val tmpTable = (caller.hardwareParam zip target.hardwareParam)
              .foldLeft(table) {
                case (acc, (caller, target)) => assign(caller, target, acc)
              }

            (caller.typeParam zip target.typeParam)
              .foldLeft(tmpTable) {
                case (acc, (caller, target)) => update(caller, target, acc)
              }
          case _ => table
        }
      }

      val assigned = (caller zip targets).foldLeft(table) {
        case (acc, (caller, target)) => update(caller, target, acc)
      }

      unwrapTable(assigned)(Error.AmbiguousHardwareParam.apply)
    }

    def assignTPTable(
      table: Map[Symbol.TypeParamSymbol, Option[Type.RefType]],
      callers: Vector[Type.RefType],
      targets: Vector[Type.RefType]
    ): Either[Error, Map[Symbol.TypeParamSymbol, Type.RefType]] = {
      def update(
        caller: Type.RefType,
        target: Type.RefType,
        table: Map[Symbol.TypeParamSymbol, Option[Type.RefType]]
      ): Map[Symbol.TypeParamSymbol, Option[Type.RefType]] =
        (caller.origin, target.origin) match {
          case (_: Symbol.EntityTypeSymbol, _: Symbol.EntityTypeSymbol) =>
            (caller.typeParam zip target.typeParam)
              .foldLeft(table) {
                case (acc, (caller, target)) => update(caller, target, acc)
              }
          case (_, tp: Symbol.TypeParamSymbol) =>
            table.get(tp) match {
              case None => throw new ImplementationErrorException(s"${tp.name} should be as key")
              case Some(None) => table.updated(tp, Some(caller))
              case Some(_) => table
            }
          case _ => throw new ImplementationErrorException("this pattern shouldn't be appeared")
        }

      val assignedTable =
        (callers zip targets)
          .foldLeft(table) {
            case (acc, (caller, target)) => update(caller, target, acc)
          }

      unwrapTable(assignedTable)(Error.AmbiguousTypeParam.apply)
    }

    def verifyHPBounds(
      swapped: Vector[HPBound],
      callerHPBound: Vector[HPBound]
    ): Either[Error, Unit] = {
      val (errs, _) = swapped.map(HPBound.verifyMeetBound(_, callerHPBound)).partitionMap(identity)

      if (errs.isEmpty) Right(())
      else Left(Error.MultipleErrors(errs: _*))
    }

    def assignMethodTpe(
      method: Type.MethodType,
      hpTable: Map[Symbol.HardwareParamSymbol, HPExpr],
      tpTable: Map[Symbol.TypeParamSymbol, Type.RefType]
    ): Type.MethodType = {
      def swapHP(expr: HPExpr): HPExpr =
        expr match {
          case ident: Ident => hpTable.getOrElse(
            ident.symbol.asHardwareParamSymbol,
            throw new ImplementationErrorException(s"hpTable should have ${ident.symbol.name}")
          )
          case HPBinOp(op, left, right) => HPBinOp(op, swapHP(left), swapHP(right))
          case lit => lit
        }

      def swapType(tpe: Type.RefType): Type.RefType =
        tpe.origin match {
          case _: Symbol.EntityTypeSymbol =>
            val swappedHP = tpe.hardwareParam.map(swapHP)
            val swappedTP = tpe.typeParam.map(swapType)

            Type.RefType(tpe.origin, swappedHP, swappedTP)
          case t: Symbol.TypeParamSymbol =>
            tpTable.getOrElse(t, throw new ImplementationErrorException(s"tpTable should have ${t.name}"))
        }

      val params = method.params.map(swapType)
      val retTpe = swapType(method.returnType)

      Type.MethodType(params, retTpe)
    }

    def verifyMethodType(
      method: Type.MethodType,
      args: Vector[Type.RefType]
    ): Either[Error, Unit] = {
      if (method.params.length != args.length) Left(Error.ParameterLengthMismatch(method.params.length, args.length))
      else {
        val (errs, _) = method.params.zip(args).map {
          case (p, a) if p =:= a => Right(())
          case (p, a) => Left(Error.TypeMismatch(p, a))
        }.partitionMap(identity)

        if (errs.isEmpty) Right(())
        else Left(Error.MultipleErrors(errs: _*))
      }
    }
  }

  object NoType extends Type {
    val name: String = "no type"
    val namespace: NameSpace = NameSpace.empty
    val declares: Scope = Scope.empty

    def =:=(other: Type): Boolean =
      throw new ImplementationErrorException("NoType is dummy type for some types of AST")
  }

  object ErrorType extends Type {
    val name: String = "error type"
    val namespace: NameSpace = NameSpace.empty
    val declares: Scope = Scope.empty

    def =:=(other: Type): Boolean = other.isErrorType
  }

  def intTpe(implicit global: GlobalData): Type.RefType = {
    val symbol = global.builtin.types.lookup("Int")
    Type.RefType(symbol)
  }

  def stringTpe(implicit global: GlobalData): Type.RefType = {
    val symbol = global.builtin.types.lookup("String")
    Type.RefType(symbol)
  }

  def unitTpe(implicit global: GlobalData): Type.RefType = {
    val symbol = global.builtin.types.lookup("Unit")
    Type.RefType(symbol)
  }

  def boolTpe(implicit global: GlobalData): Type.RefType = {
    val symbol = global.builtin.types.lookup("Bool")
    Type.RefType(symbol)
  }

  def bitTpe(width: IntLiteral)(implicit global: GlobalData): Type.RefType = {
    val symbol = global.builtin.types.lookup("Bit")
    val IntLiteral(value) = width

    if (value > 0) Type.RefType(symbol, Vector(width), Vector.empty)
    else throw new ImplementationErrorException(s"Bit's width[${value}] must be natural number")
  }

  def futureTpe(targ: Type.RefType)(implicit global: GlobalData): Type.RefType = {
    val symbol = global.builtin.types.lookup("Future")
    Type.RefType(symbol, Vector.empty, Vector(targ))
  }

  def numTpe(implicit global: GlobalData): Type.RefType = {
    val symbol = global.builtin.types.lookup("Num")
    Type.RefType(symbol, Vector.empty, Vector.empty)
  }

  def strTpe(implicit global: GlobalData): Type.RefType = {
    val symbol = global.builtin.types.lookup("Str")
    Type.RefType(symbol, Vector.empty, Vector.empty)
  }

  def buildType[T <: Symbol.TypeSymbol](typeTree: TypeTree)(implicit ctx: Context.NodeContext, global: GlobalData, ev0: ClassTag[T], ev1: TypeTag[T]): (Option[Error], TypeTree) = {
    def typeCheckHardArgs(symbol: Symbol.TypeSymbol, hargs: Vector[HPExpr]): Either[Error, Unit] = {
      val errs = (symbol.hps.map(_.tpe) zip hargs.map(_.tpe))
        .filterNot { case (e, a) => e == a }
        .map { case (e, a) => Error.TypeMismatch(e, a) }

      if(errs.isEmpty) Right(())
      else Left(Error.MultipleErrors(errs: _*))
    }

    def buildForIdent(ident: Ident, hargs: Vector[HPExpr], targs: Vector[TypeTree]): (Option[Error], TypeTree) = {
      val result = for {
        symbol <- ctx.lookup[T](ident.name).toEither
        polyArgs <- buildParams(symbol, hargs, targs)
        (typedHArgs, typedTArgs) = polyArgs
        _ <- typeCheckHardArgs(symbol, typedHArgs)
      } yield {
        TypeTree(ident, typedHArgs, typedTArgs)
          .setSymbol(symbol)
          .setTpe(Type.RefType(symbol, typedHArgs, typedTArgs.map(_.tpe.asRefType)))
          .setID(typeTree.id)
      }

      result match {
        case Left(err) => (Some(err), typeTree.setSymbol(Symbol.ErrorSymbol).setTpe(Type.ErrorType))
        case Right(tree) => (None, tree)
      }
    }

    def buildForSelectPackage(select: SelectPackage, hargs: Vector[HPExpr], targs: Vector[TypeTree]): (Option[Error], TypeTree) = {
      lazy val packageLookupFromCtx = ctx.lookup[Symbol.PackageSymbol](select.packages.head).toEither
      lazy val packageLookupFromRoot = global.rootPackage.search(Vector(select.packages.head))
      val packageLookup = packageLookupFromCtx.left.flatMap(_ => packageLookupFromRoot)

      val pkgResult = select.packages.tail.foldLeft(packageLookup) {
        case (Left(err), _) => Left(err)
        case (Right(symbol), name) => symbol.lookup[Symbol.PackageSymbol](name).toEither
      }

      val result = for {
        pkgSymbol <- pkgResult
        typeSymbol <- pkgSymbol.lookup[Symbol.TypeSymbol](select.name).toEither
        args <- buildParams(typeSymbol, hargs, targs)
        (typedHArgs, typedTArgs) = args
        _ <- typeCheckHardArgs(typeSymbol, typedHArgs)
      } yield {
        val targTpes = typedTArgs.map(_.tpe.asRefType)
        val tpe = Type.RefType(typeSymbol, typedHArgs, targTpes)
        val typedSelect = select.setSymbol(typeSymbol).setTpe(tpe)

        TypeTree(typedSelect, typedHArgs, typedTArgs)
          .setSymbol(typeSymbol)
          .setTpe(tpe)
          .setID(typeTree.id)
      }

      result match {
        case Right(tree) => (None, tree)
        case Left(err) => (Some(err), typeTree.setTpe(Type.ErrorType).setSymbol(Symbol.ErrorSymbol))
      }
    }

    typeTree.expr match {
      case ident: Ident => buildForIdent(ident, typeTree.hp, typeTree.tp)
      case select: SelectPackage => buildForSelectPackage(select, typeTree.hp, typeTree.tp)
      case select: StaticSelect =>
        val err = Some(Error.CannotUseStaticSelect(select))
        val tree = typeTree.setTpe(Type.ErrorType).setSymbol(Symbol.ErrorSymbol)

        (err, tree)
    }
  }

  private def buildHP(hp: HPExpr)(implicit ctx: Context.NodeContext, global: GlobalData): (Option[Error], HPExpr) = {
    hp match {
      case lit: IntLiteral => (None, lit.setTpe(Type.numTpe))
      case lit: StringLiteral => (None, lit.setTpe(Type.strTpe))
      case ident @ Ident(name) => ctx.lookup[Symbol.HardwareParamSymbol](name) match {
        case LookupResult.LookupFailure(err) => (Some(err), ident.setSymbol(Symbol.ErrorSymbol).setTpe(Type.ErrorType))
        case LookupResult.LookupSuccess(symbol) => (None, ident.setSymbol(symbol).setTpe(symbol.tpe))
      }
      case HPBinOp(op, left, right) =>
        val (err0, builtLeft) = buildHP(left)
        val (err1, builtRight) = buildHP(right)

        val errs0 = Vector(err0, err1).flatten
        val errs1 =
          if (builtLeft.tpe =!= Type.numTpe && builtLeft.tpe =!= Type.ErrorType) errs0 :+ Error.TypeMismatch(Type.numTpe, builtLeft.tpe)
          else if (builtRight.tpe =!= Type.numTpe && builtLeft.tpe =!= Type.ErrorType) errs0 :+ Error.TypeMismatch(Type.numTpe, builtRight.tpe)
          else errs0

        val (errs, tpe) =
          if (errs1.isEmpty) (None, Type.numTpe)
          else (Some(Error.MultipleErrors(errs1: _*)), Type.ErrorType)

        (errs, HPBinOp(op, builtLeft, builtRight).setTpe(tpe))
    }
  }

  private def buildParams(symbol: Symbol.TypeSymbol, hps: Vector[HPExpr], tps: Vector[TypeTree])(implicit ctx: Context.NodeContext, global: GlobalData): Either[Error, (Vector[HPExpr], Vector[TypeTree])] = {
    def verifyLength: Either[Error, Unit] = {
      def verify(expect: Int, actual: Int, builder: (Int, Int) => Error): Either[Error, Unit] =
        if (expect == actual) Right(())
        else Left(builder(expect, actual))

      Vector(
        verify(symbol.hps.length, hps.length, Error.HardParameterLengthMismatch.apply),
        verify(symbol.tps.length, tps.length, Error.TypeParameterLengthMismatch.apply)
      ).combine(errs => Error.MultipleErrors(errs: _*))
    }

    verifyLength match {
      case Left(err) => Left(err)
      case Right(_) =>
        val (hpErrs, builtHPs) = hps.map(buildHP).unzip
        val (tpErrs, builtTPs) = tps.map(buildType[Symbol.TypeSymbol]).unzip

        val allErrs = hpErrs.flatten ++ tpErrs.flatten

        if (allErrs.isEmpty) Right(builtHPs.map(_.sort), builtTPs)
        else Left(Error.MultipleErrors(allErrs: _*))
    }
  }

  def buildThisType(symbol: Symbol.TypeSymbol, hps: Vector[ValDef], tps: Vector[TypeDef])(implicit ctx: Context.NodeContext, global: GlobalData): Option[Type.RefType] = {
    val hasError = hps.exists(_.symbol.tpe.isErrorType)

    val typedHargs = hps.map(hp => Ident(hp.name).setSymbol(hp.symbol).setTpe(hp.symbol.tpe))
    val typedTargs = tps.map{
      tp =>
        val tpSymbol = tp.symbol.asTypeParamSymbol
        Type.RefType(tpSymbol, Vector.empty, Vector.empty)
    }

    if(hasError) None
    else Some(Type.RefType(symbol, typedHargs, typedTargs))
  }
}