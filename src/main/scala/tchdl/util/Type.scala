package tchdl.util

import tchdl.ast._
import tchdl.typecheck.{ImplementContainer, ImplementInterfaceContainer, Namer, Typer}
import tchdl.util.TchdlException.ImplementationErrorException

import scala.reflect.ClassTag
import scala.reflect.runtime.universe.TypeTag

trait Type {
  def name: String
  def namespace: NameSpace
  protected def declares: Scope

  def asRefType: Type.RefType = this.asInstanceOf[Type.RefType]
  def asEntityType: Type.EntityType = this.asInstanceOf[Type.EntityType]
  def asParameterType: Type.TypeParamType = this.asInstanceOf[Type.TypeParamType]
  def asMethodType: Type.MethodType = this.asInstanceOf[Type.MethodType]

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

  case class ModuleTypeGenerator(module: ModuleDef, ctx: Context.RootContext, global: GlobalData) extends TypeGenerator {
    override def generate: Type.EntityType = {
      val fieldCtx = Context(ctx, module.symbol)
      module.parents.map(Namer.namedValDef(_)(fieldCtx, global))
      module.siblings.map(Namer.namedValDef(_)(fieldCtx, global))

      Type.EntityType(module.name, ctx.path, fieldCtx.scope)
    }
  }

  case class StructTypeGenerator(struct: StructDef, ctx: Context.RootContext, global: GlobalData) extends TypeGenerator {
    override def generate: Type.EntityType = {
      val fieldCtx = Context(ctx, struct.symbol)
      struct.fields.map(Namer.nodeLevelNamed(_)(fieldCtx, global))

      EntityType(struct.name, ctx.path, fieldCtx.scope)
    }
  }

  case class InterfaceTypeGenerator(interface: InterfaceDef, ctx: Context.RootContext, global: GlobalData) extends TypeGenerator {
    override def generate: Type.EntityType = {
      val interfaceCtx = Context(ctx, interface.symbol)
      interface.methods.map(Namer.nodeLevelNamed(_)(interfaceCtx, global))

      EntityType(interface.name, ctx.path, interfaceCtx.scope)
    }
  }

  case class MethodTypeGenerator(method: MethodDef, ctx: Context.NodeContext, global: GlobalData) extends TypeGenerator {
    override def generate: Type.MethodType = {
      val signatureCtx = Context(ctx, method.symbol)
      signatureCtx.reAppend(
        method.symbol.asMethodSymbol.hps ++
        method.symbol.asMethodSymbol.tps: _*
      )(global)

      val paramTpes = method.params
        .map(Namer.nodeLevelNamed(_)(signatureCtx, global))
        .map(Typer.typedValDef(_)(signatureCtx, global))
        .map(_.symbol.tpe.asRefType)
      val retTpes = Typer.typedTypeTree(method.retTpe)(signatureCtx, global).tpe.asRefType

      MethodType(paramTpes, retTpes)
    }
  }

  case class VariableTypeGenerator(vdef: ValDef, ctx: Context.NodeContext, global: GlobalData) extends TypeGenerator {
    override def generate: Type = {
      val ValDef(_, _, tpeTree, expr) = vdef

      (tpeTree, expr) match {
        case (None, None) =>
          global.repo.error.append(Error.RequireType)
          Type.ErrorType
        case (None, Some(expr)) =>
          val typedExp = Typer.typedExpr(expr)(ctx, global)
          typedExp.tpe
        case (Some(tpe), _) =>
          val typedTpe = Typer.typedTypeTree(tpe)(ctx, global)
          typedTpe.tpe
      }
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
              global.repo.error.append(Error.RequireNumOrStr(tpe))
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

    def =:=(other: Type): Boolean = other match {
      case other: MethodType =>
        def isSameParam: Boolean = this.params == other.params
        def isSameRet: Boolean = this.returnType == other.returnType

        isSameParam && isSameRet
    }
  }

  object MethodType {
    def apply(args: Vector[Type.RefType], retTpe: RefType): MethodType = new MethodType(args, retTpe)
  }

  class RefType(
    val origin: Symbol.TypeSymbol,
    val hardwareParam: Vector[HPExpr],
    val typeParam: Vector[Type.RefType]
  ) extends Type {
    val name: String = origin.name
    val namespace: NameSpace = origin.path

    override def declares: Scope = origin.tpe.declares

    def lookupField(name: String): LookupResult[Symbol.TermSymbol] = {
      def lookupToClass: LookupResult[Symbol.TermSymbol] =
        origin.tpe.declares.lookup(name) match {
          // TODO: verify whether this logic needs to replace type parameter into actual type or not
          case Some(symbol: Symbol.TermSymbol) => LookupResult.LookupSuccess(symbol)
          case Some(symbol) => LookupResult.LookupFailure(Error.RequireSymbol[Symbol.TermSymbol](symbol))
          case None => LookupResult.LookupFailure(Error.SymbolNotFound(name))
        }

      this.origin match {
        case _: Symbol.ClassTypeSymbol => lookupToClass
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
      ctx: Context.NodeContext
    ): LookupResult[(Symbol.MethodSymbol, Type.MethodType)] = {
      val result = this.origin match {
        case entity: Symbol.EntityTypeSymbol =>
          lookupFromImpls(
            entity.impls,
            methodName,
            args,
            callerHP,
            callerTP,
            callerHPBound,
            callerTPBound
          ) match {
            case success @ Right(_) => success
            case Left(_) if ctx.interfaceTable.isEmpty => Left(Error.SymbolNotFound(methodName))
            case Left(_) =>
              val (errs, methods) = ctx.interfaceTable
                .values.view
                .map(_.impls)
                .map(lookupFromImpls(_, methodName, args, callerHP, callerTP, callerHPBound, callerTPBound))
                .to(Vector)
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
                    callerTPBound
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
    ): Either[Error, (Symbol.MethodSymbol, Type.MethodType)] = {
      val (initHpTable, initTpTable) = RefType.buildTable(impl)
      val lookupResult = impl.lookup[Symbol.MethodSymbol](methodName) match {
        case None => Left(Error.SymbolNotFound(methodName))
        case Some(symbol) => Right(symbol)
      }

      def verifyEachBounds(hpBounds: Vector[HPBound], tpBounds: Vector[TPBound]): Either[Error, Unit] = {
        val (hpErrs, _) = hpBounds
          .map(HPBound.verifyMeetBound(_, callerHPBound))
          .partitionMap(identity)

        val (tpErrs, _) = tpBounds
          .map(TPBound.verifyMeetBound(_, callerHPBound, callerTPBound))
          .partitionMap(identity)

        val errs = hpErrs ++ tpErrs
        if(errs.isEmpty) Right(())
        else Left(Error.MultipleErrors(errs: _*))
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
        _ <- verifyEachBounds(simplifiedHPBound, swappedTpBound)
        (methodHpTable, methodTpTable) = RefType.buildSymbolTable(method, callerHP, callerTP)
        appendHpTable = hpTable ++ methodHpTable
        appendTpTable = tpTable ++ methodTpTable
        methodHpBound = HPBound.swapBounds(method.hpBound, appendHpTable)
        methodTpBound = TPBound.swapBounds(method.tpBound, appendHpTable, appendTpTable)
        _ <- verifyEachBounds(methodHpBound, methodTpBound)
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
      callerTPBound: Vector[TPBound]
    ): Either[Error, (Symbol.MethodSymbol, Type.MethodType)] = {
      val (initHpTable, initTpTable) = RefType.buildSymbolTable(interface, interfaceHPs, interfaceTPs)
      val lookupResult = interface.tpe.declares.lookup(methodName) match {
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
        if(errs.isEmpty) Right(())
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
      callerTPBound: Vector[TPBound]
    ): Either[Error, (Symbol.MethodSymbol, Type.MethodType)] = {
      impls.foldLeft[Either[Error, (Symbol.MethodSymbol, Type.MethodType)]](Left(Error.DummyError)) {
        case (right @  Right(_), _) => right
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
            case right @ Right(_) => right
            case Left(err) => Left(Error.MultipleErrors(err, errs))
          }
      }
    }

    def lookupOperation(
      op: Operation,
      arg: Type.RefType,
      callerHPBounds: Vector[HPBound],
      callerTPBounds: Vector[TPBound],
      ctx: Context.NodeContext
    ): LookupResult[(Symbol.MethodSymbol, Type.MethodType)] = {
      ctx.interfaceTable.get(op.toInterface) match {
        case None => LookupResult.LookupFailure(Error.OperationNotFound(op))
        case Some(interface) =>
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
      }
    }

//    def lookupMethod2(
//      methodName: String,
//      hardArgs: Vector[HPExpr],
//      typeArgs: Vector[Type.RefType],
//      args: Vector[Type.RefType]
//    )(implicit ctx: Context): LookupResult[(Symbol.MethodSymbol, Type.MethodType)] = {
//      def buildTable[K, V](keys: Vector[K]): Map[K, Option[V]] = keys.map((_, Option.empty[V])).toMap
//
//
//      def unwrap[K, V](table: Map[K, Option[V]]): Either[Error, Map[K, V]] = {
//        val (errs, unwrapped) = table.map {
//          case (key, Some(value)) => Right(key -> value)
//          case (key, None) => Left(???)
//        }.partitionMap(identity)
//
//        if (errs.isEmpty) Right(unwrapped.toMap)
//        else Left(Error.MultipleErrors(errs.toVector))
//      }
//
//      def unwrapTables(
//        hpTable: Map[Symbol.HardwareParamSymbol, Option[HPExpr]],
//        tpTable: Map[Symbol.TypeParamSymbol, Option[Type.RefType]]
//      ): Either[Error, (Map[Symbol.HardwareParamSymbol, HPExpr], Map[Symbol.TypeParamSymbol, Type.RefType])] = {
//        (unwrap(hpTable), unwrap(tpTable)) match {
//          case (Right(hp), Right(tp)) => Right((hp, tp))
//          case (Left(hpErr), Left(tpErr)) => Left(Error.MultipleErrors(hpErr, tpErr))
//          case (Left(err), _) => Left(err)
//          case (_, Left(err)) => Left(err)
//        }
//      }
//
//      def update[K <: Symbol, V](symbol: K, value: V, table: Map[K, Option[V]]): Map[K, Option[V]] =
//        table.get(symbol) match {
//          case None => throw new ImplementationErrorException(s"table does not have ${symbol.name} as key")
//          case Some(None) => table.updated(symbol, Some(value))
//          case Some(_) => table
//        }
//
//      def updateMultiple[K <: Symbol, V](params: Vector[K], args: Vector[V], table: Map[K, Option[V]])(reject: V => : Map[K, Option[V]] =
//        params.zip(args).foldLeft(table) {
//          case (table, (p, a)) => update(p, a, table)
//        }
//
//      def assignHP(param: Type.RefType, arg: Type.RefType)(tab: Map[Symbol.HardwareParamSymbol, Option[HPExpr]]): Map[Symbol.HardwareParamSymbol, Option[HPExpr]] = {
//        val table = param.hardwareParam.zip(arg.hardwareParam)
//          .foldLeft(tab) {
//            case (tab, (paramExpr: Ident, argExpr)) =>
//              val hp = paramExpr.symbol.asHardwareParamSymbol
//              update(hp, argExpr, tab)
//            case (tab, (_, _)) => tab
//          }
//
//        assignHPs(param.typeParam, arg.typeParam)(table)
//      }
//
//      def assignHPs(params: Vector[Type.RefType], args: Vector[Type.RefType])(tab: Map[Symbol.HardwareParamSymbol, Option[HPExpr]]): Map[Symbol.HardwareParamSymbol, Option[HPExpr]] =
//        params.zip(args).foldLeft(tab) {
//          case (table, (param, arg)) => assignHP(param, arg)(table)
//        }
//
//      def assignTP(param: Type.RefType, arg: Type.RefType)(table: Map[Symbol.TypeParamSymbol, Option[Type.RefType]]): Map[Symbol.TypeParamSymbol, Option[Type.RefType]] =
//        param.origin match {
//          case tp: Symbol.TypeParamSymbol => update(tp, arg, table)
//          case _: Symbol.EntityTypeSymbol => assignTPs(param.typeParam, arg.typeParam)(table)
//        }
//
//      def assignTPs(params: Vector[Type.RefType], args: Vector[Type.RefType])(tab: Map[Symbol.TypeParamSymbol, Option[Type.RefType]]): Map[Symbol.TypeParamSymbol, Option[Type.RefType]] =
//        params.zip(args).foldLeft(tab) {
//          case (table, (param, arg)) => assignTP(param, arg)(table)
//        }
//
//      def verifyLength(methodTpe: Type.MethodType): Either[Error, Unit] = {
//        val expects = Vector(
//          methodTpe.typeParam.length,
//          methodTpe.hardwareParam.length,
//          methodTpe.params.length
//        )
//
//        val actuals = Vector(
//          typeArgs.length,
//          hardArgs.length,
//          args.length
//        )
//
//        val errContainers = Vector(
//          Error.TypeParameterLengthMismatch.apply _,
//          Error.HardParameterLengthMismatch.apply _,
//          Error.ParameterLengthMismatch.apply _
//        )
//
//        val errs = (expects, actuals, errContainers).zipped.foldLeft(Vector.empty[Error]) {
//          case (errs, (expect, actual, container)) =>
//            if (expect == actual) errs
//            else errs :+ container(expect, actual)
//        }
//
//        if (errs.isEmpty) Right(())
//        else Left(Error.MultipleErrors(errs))
//      }
//
//      def verifyTypeArg(
//        method: Symbol.MethodSymbol,
//        hpTable: Map[Symbol.HardwareParamSymbol, HPExpr],
//        tpTable: Map[Symbol.TypeParamSymbol, Type.RefType]
//      ): Either[Error, Unit] = {
//        val tps = method.tpe.asMethodType.typeParam
//        tps.map {
//          tp => tp.getBounds.map(_.replaceWithMap(tpTable))
//        }
//
//        val errs =
//          methodTpe.typeParam.zip(typeArgs).foldLeft(Vector.empty[Error]) {
//            case (errs, (param, arg)) =>
//              if (arg <|= Type.RefType(param)) errs
//              else errs :+ Error.NotMeetBound(arg, param.getBounds)
//          }
//
//        if (errs.isEmpty) Right(())
//        else Left(Error.MultipleErrors(errs))
//      }
//
//      def verifyHardArg(
//        method: Symbol.MethodSymbol,
//        hpTable: Map[Symbol.HardwareParamSymbol, HPExpr]
//      ): Either[Error, Unit] = {
//        val callerBounds = ctx.allHPBounds
//        val calledBounds = method.getHPBounds
//
//        HPExpr.verifyHPBound(calledBounds, callerBounds, hpTable)
//      }
//
//      def verifyArgTypes(methodTpe: Type.MethodType): Either[Error, Unit] = {
//        val (errs, _) = methodTpe.params.zip(args).map {
//          case (param, arg) if param =:= arg => Right(())
//          case (param, arg) => Left(???)
//        }.partitionMap(identity)
//
//        if (errs.isEmpty) Right(())
//        else Left(Error.MultipleErrors(errs))
//      }
//
//      def lookupIntoClassImpl(tpe: Symbol.ClassTypeSymbol): Either[Error, (Symbol.MethodSymbol, Type.MethodType)] = {
//        def lookupImpl: Either[Error, ImplementClassContainer] = {
//          tpe.lookupImpl(this) match {
//            case Vector() => Left(Error.DummyError)
//            case Vector(impl) => Right(impl)
//            case _ => throw new ImplementationErrorException("multiple impl is detected from one Ref Type")
//          }
//        }
//
//        for {
//          impl <- lookupImpl
//          method <- impl.lookup[Symbol.MethodSymbol](methodName).map(Right.apply).getOrElse(Left(Error.DummyError))
//          methodTpe = method.tpe.asMethodType
//          _ <- verifyLength(methodTpe)
//          tpTable0 = buildTable[Symbol.TypeParamSymbol, Type.RefType](impl.typeParam ++ methodTpe.typeParam)
//          hpTable0 = buildTable[Symbol.HardwareParamSymbol, HPExpr](impl.hardwareParam ++ methodTpe.hardwareParam)
//          tpTable1 = assignTP(impl.targetType, this)(tpTable0)
//          hpTable1 = assignHP(impl.targetType, this)(hpTable0)
//          tpTable2 = updateMultiple(methodTpe.typeParam, typeArgs, tpTable1)
//          hpTable2 = updateMultiple(methodTpe.hardwareParam, hardArgs, hpTable1)
//          tpTable3 = assignTPs(methodTpe.params, args)(tpTable2)
//          hpTable3 = assignHPs(methodTpe.params, args)(hpTable2)
//          tables <- unwrapTables(hpTable3, tpTable3)
//          (hpTable, tpTable) = tables
//          _ <- verifyHardArg(method, hpTable)
//          _ <- verifyTypeArg(method, hpTable, tpTable)
//          replacedMethodTpe = methodTpe.replaceWithMap(hpTable, tpTable)
//          _ <- verifyArgTypes(replacedMethodTpe)
//        } yield (method, replacedMethodTpe)
//      }
//
//      def lookupIntoInterfaceImpl(): Either[Error, (Symbol.MethodSymbol, Type.MethodType)] = {
//        val pairs = for {
//          interface <- ctx.interfaceTable.values
//          impl <- interface.lookupImpl(this)
//          interfaceTpe = interface.tpe
//          symbol = interfaceTpe.declares.lookup(methodName)
//          methodSymbol <- symbol.collect { case method: Symbol.MethodSymbol => method }
//        } yield (impl, methodSymbol)
//
//        val (errs, candidates) = pairs.map {
//          case (impl, method) =>
//            val implTpTable0 = buildTable(impl.typeParam)
//            val implHpTable0 = buildTable(impl.hardwareParam)
//            val implTpTable1 = assignTP(impl.targetType, this)(implTpTable0)
//            val implHpTable1 = assignHP(impl.targetType, this)(implHpTable0)
//            val methodTpe = method.tpe.asMethodType
//            val interfaceTpe = impl.targetInterface.origin.tpe.asEntityType
//
//            for {
//              _ <- verifyLength(methodTpe)
//              implTables <- unwrapTables(implHpTable1, implTpTable1)
//              (implHpTable, implTpTable) = implTables
//              actualInterface = impl.targetInterface.replaceWithMap(implHpTable, implTpTable)
//              tpTable0 = buildTable[Symbol.TypeParamSymbol, Type.RefType](interfaceTpe.typeParam ++ methodTpe.typeParam)
//              hpTable0 = buildTable[Symbol.HardwareParamSymbol, HPExpr](interfaceTpe.hardwareParam ++ methodTpe.hardwareParam)
//              tpTable1 = updateMultiple(interfaceTpe.typeParam, actualInterface.typeParam, tpTable0)
//              hpTable1 = updateMultiple(interfaceTpe.hardwareParam, actualInterface.hardwareParam, hpTable0)
//              tpTable2 = updateMultiple(methodTpe.typeParam, typeArgs, tpTable1)
//              hpTable2 = updateMultiple(methodTpe.hardwareParam, hardArgs, hpTable1)
//              tpTable3 = assignTPs(methodTpe.params, args)(tpTable2)
//              hpTable3 = assignHPs(methodTpe.params, args)(hpTable2)
//              tables <- unwrapTables(hpTable3, tpTable3)
//              (hpTable, tpTable) = tables
//              _ <- verifyHardArg(method, hpTable)
//              _ <- verifyTypeArg(method, hpTable, tpTable)
//              replacedMethodTpe = methodTpe.replaceWithMap(hpTable, tpTable)
//              _ <- verifyArgTypes(replacedMethodTpe)
//              methodSymbol = impl
//                .lookup[Symbol.MethodSymbol](methodName)
//                .getOrElse(throw new ImplementationErrorException(s"$methodName was not found in Implementation"))
//            } yield (methodSymbol, replacedMethodTpe)
//        }.partitionMap(identity)
//
//        candidates.toVector match {
//          case Vector() => Left(Error.MultipleErrors(errs.toVector))
//          case Vector(method) => Right(method)
//          case methods => Left(Error.AmbiguousSymbols(methods.map(_._1)))
//        }
//      }
//
//      val methodPair = this.origin match {
//        case _: Symbol.TypeParamSymbol =>
//          lookupIntoInterfaceImpl()
//        case origin: Symbol.ClassTypeSymbol =>
//          val res = for {
//            _ <- lookupIntoClassImpl(origin).swap
//            errs <- lookupIntoInterfaceImpl().swap
//          } yield errs
//
//          res.swap
//      }
//
//      methodPair match {
//        case Right(pair) => LookupResult.LookupSuccess(pair)
//        case Left(errs) => LookupResult.LookupFailure(errs)
//      }
//    }

    /*
    def lookupMethod(name: String, tp: Vector[Type.RefType], args: Vector[Type.RefType])(implicit ctx: Context): LookupResult[Symbol.MethodSymbol] = {
      val specificTpeImplMethod = this.origin match {
        case origin: Symbol.EntityTypeSymbol => origin.lookupImpl(this) match {
          case Vector() => None
          case Vector(impl) => impl.lookup[Symbol.MethodSymbol](name)
          case _ =>
            val msg = "Multiple implementations are detected. However, this case must not be happened because implementation conflict is already detected before phase"
            throw new ImplementationErrorException(msg)
        }
        case _: Symbol.TypeParamSymbol => None
      }

      specificTpeImplMethod match {
        case Some(result) => LookupResult.LookupSuccess(result)
        case None =>
          // For the case of reference to type parameter
          val symbols = ctx.interfaceTable.values
            .flatMap(_.lookupImpl(this))
            .flatMap(_.lookup[Symbol.MethodSymbol](name))
            .toVector

          symbols match {
            case Vector(symbol) => LookupResult.LookupSuccess(symbol)
            case Vector() => LookupResult.LookupFailure(Error.SymbolNotFound(name))
            case symbols => LookupResult.LookupFailure(Error.AmbiguousSymbols(symbols))
          }
      }
    }
     */

    // TODO: lookup type that is defined at implementation
    def lookupType(name: String): LookupResult[Symbol.TypeSymbol] = {
      def lookupToTypeParam(tp: Symbol.TypeParamSymbol): LookupResult[Symbol.TypeSymbol] = ???

      this.origin match {
        case origin: Symbol.TypeParamSymbol => lookupToTypeParam(origin)
        case origin: Symbol.EntityTypeSymbol => LookupResult.LookupFailure(Error.RejectEntityTypeFromLookup(origin))
      }
    }

    def replaceWithMap(hpMap: Map[Symbol.HardwareParamSymbol, HPExpr], tpMap: Map[Symbol.TypeParamSymbol, Type.RefType]): Type.RefType = {
      def replaceHP(expr: HPExpr): HPExpr = expr match {
        case ident: Ident => hpMap.getOrElse(ident.symbol.asHardwareParamSymbol, ident)
        case binop: HPBinOp => HPBinOp(binop.op, replaceHP(binop.left), replaceHP(binop.right))
        case others => others
      }

      origin match {
        case symbol: Symbol.TypeParamSymbol => tpMap.getOrElse(symbol, this)
        case _ => RefType(
          this.origin,
          this.hardwareParam.map(replaceHP),
          typeParam.map(_.replaceWithMap(hpMap, tpMap))
        )
      }
    }


    override def =:=(other: Type): Boolean = other match {
      case other: RefType =>
        def isSameOrigin = this.origin == other.origin

        def isSameHpType = {
          def isSameLength = this.hardwareParam.length == other.hardwareParam.length

          def isSameType = this.hardwareParam
            .zip(other.hardwareParam)
            .forall { case (t, o) => t.tpe =:= o.tpe }

          isSameLength && isSameType
        }

        def isSameTP = {
          def isSameLength = this.typeParam.length == other.typeParam.length

          def isSameTypes = (this.typeParam zip other.typeParam).forall { case (t, o) => t =:= o }

          isSameLength && isSameTypes
        }

        isSameOrigin && isSameHpType && isSameTP
    }

    override def equals(obj: Any): Boolean = obj match {
      case other: RefType =>
        def isSameHP = this.hardwareParam == other.hardwareParam

        this =:= other && isSameHP
    }

    override def toString: String = {
      val name = this.origin.name
      val hps = this.hardwareParam.map(_.toString).mkString(", ")
      val tps = this.typeParam.map(_.toString).mkString(", ")
      val params =
        if (this.typeParam.isEmpty && this.hardwareParam.isEmpty) ""
        else if(this.hardwareParam.isEmpty) s"[$tps]"
        else if (this.typeParam.isEmpty) s"[$hps]"
        else s"[$hps, $tps]"

      s"$name$params"
    }

    /*
    def isOverlapped(
      that: Type.RefType,
      thisHpBounds: Vector[HPBound],
      thatHpBounds: Vector[HPBound],
      thisTpBounds: Vector[TPBound],
      thatTpBounds: Vector[TPBound],
    ): Boolean = {
      def compareBothEntity(t0: Symbol.EntityTypeSymbol, t1: Symbol.EntityTypeSymbol): Boolean = {
        def isSameType: Boolean = t0 == t1

        def isOverlappedHP: Boolean = {
          def findRange(expr: HPExpr, bounds: Vector[HPBound]): HPRange.Range =
            bounds.find(_.target.isSameExpr(expr))
              .map(_.bound)
              .collect { case range: HPRange.Range => range }
              .getOrElse(HPRange.Range.empty)

          def findEqual(expr: HPExpr, bounds: Vector[HPBound]): Option[HPRange.Eq] = {
            bounds.find(_.target.isSameExpr(expr))
              .map(_.bound)
              .collect { case eq: HPRange.Eq => eq }
          }

          this.hardwareParam.zip(that.hardwareParam).forall {
            case (IntLiteral(int0), IntLiteral(int1)) => int0 == int1
            case (StringLiteral(str0), StringLiteral(str1)) => str0 == str1
            case (_: HPExpr, _: StringLiteral) => false
            case (_: StringLiteral, _: HPExpr) => false
            case (IntLiteral(int), expr: HPExpr) =>
              findEqual(expr, thatHpBounds)
                .map(_.isOverlapped(int))
                .getOrElse(findRange(expr,thatHpBounds).isOverlapped(int))
            case (expr: HPExpr, IntLiteral(int)) =>
              findEqual(expr, thatHpBounds)
                .map(_.isOverlapped(int))
                .getOrElse(findRange(expr,thatHpBounds).isOverlapped(int))
            case (expr0: HPExpr, expr1: HPExpr) =>
              val thisEqual = findEqual(expr0, thisHpBounds)
              val thatEqual = findEqual(expr1, thatHpBounds)
              (thisEqual, thatEqual) match {
                case (Some(eq0), Some(eq1)) => eq0.isOverlapped(eq1)
                case (Some(eq), None) => findRange(expr1, thatHpBounds).isOverlapped(eq)
                case (None, Some(eq)) => findRange(expr0, thisHpBounds).isOverlapped(eq)
                case (None, None) => findRange(expr0, thisHpBounds).isOverlapped(findRange(expr1, thatHpBounds))
              }
          }
        }

        isSameType &&
          isOverlappedHP &&
          this.typeParam.zip(that.typeParam)
            .forall { case (t0, t1) =>
              t0.isOverlapped(t1, thisHpBounds, thatHpBounds, thisTpBounds, thatTpBounds)
            }
      }

      def entityAndTypeParam(entity: Symbol.EntityTypeSymbol, tp: Symbol.TypeParamSymbol, hpBounds: Vector[HPBound], tpBounds: Vector[TPBound]): Boolean = {
        def verify(bound: Type.RefType, impls: Vector[ImplementInterfaceContainer]): Boolean =
          impls.exists { impl =>
            val isInterfaceOverlapped = bound.isOverlapped(
              impl.targetInterface,
              hpBounds,
              impl.symbol.hpBound,
              tpBounds,
              impl.symbol.tpBound
            )

            val isTargetOverlapped = this.isOverlapped(
              impl.targetType,
              thisHpBounds,
              impl.symbol.hpBound,
              thisTpBounds,
              impl.symbol.tpBound
            )

            isInterfaceOverlapped && isTargetOverlapped
          }

        val bounds = tpBounds
          .find(_.target.origin == tp)
          .map(_.bounds)

        bounds match {
          case None => true
          case Some(bounds) =>
            val implss = bounds.view
              .map(_.origin)
              .map(_.asInterfaceSymbol)
              .map(_.impls)
              .toVector

            bounds.zip(implss).exists { case (bound, impls) => verify(bound, impls) }
        }
      }


      (this.origin, that.origin) match {
        case (t0: Symbol.EntityTypeSymbol, t1: Symbol.EntityTypeSymbol) => compareBothEntity(t0, t1)
        case (entity: Symbol.EntityTypeSymbol, tp: Symbol.TypeParamSymbol) => entityAndTypeParam(entity, tp)
        case (tp: Symbol.TypeParamSymbol, entity: Symbol.EntityTypeSymbol) => entityAndTypeParam(entity, tp)
        case (_: Symbol.TypeParamSymbol, _: Symbol.TypeParamSymbol) => true
      }
    }
     */

    /*
    def isSubsetOf(
      that: Type.RefType,
      thisHpBounds: Vector[HPBound],
      thatHpBounds: Vector[HPBound],
      thisTpBounds: Vector[TPBound],
      thatTpBounds: Vector[TPBound]
    ): Boolean = {
      def compareBothEntity(t0: Symbol.EntityTypeSymbol, t1: Symbol.EntityTypeSymbol): Boolean = {
        def isSameSymbol: Boolean = t0 == t1

        def isSubsetHP: Boolean = {
          def getRange(expr: HPExpr, hpBounds: Vector[HPBound]): HPRange =
            hpBounds
              .find(_.target.isSameExpr(expr))
              .map(_.range)
              .getOrElse(HPRange.Range.empty)

          this.hardwareParam.zip(that.hardwareParam).forall {
            case (IntLiteral(v0), IntLiteral(v1)) => v0 == v1
            case (StringLiteral(str0), StringLiteral(str1)) => str0 == str1
            case (_: HPExpr, _: StringLiteral) => false
            case (_: StringLiteral, _: HPExpr) => false
            case (IntLiteral(value), expr: HPExpr) => getRange(expr, thatHpBounds).isOverlapped(value)
            case (expr: HPExpr, IntLiteral(value)) => getRange(expr, thisHpBounds).isSubsetOf(value)
            case (e0: HPExpr, e1: HPExpr) => getRange(e0, thisHpBounds).isSubsetOf(getRange(e1, thatHpBounds))
          }
        }

        isSameSymbol &&
          isSubsetHP &&
          this.typeParam.zip(that.typeParam)
            .forall { case (t0, t1) =>
              t0.isSubsetOf(
                t1,
                thisHpBounds,
                thatHpBounds,
                thisTpBounds,
                thatTpBounds
              )
            }
      }
     */

    /*
      def compareEntityAndTypeParam(entity: Symbol.EntityTypeSymbol, tp: Symbol.TypeParamSymbol): Boolean = {
        thatTpBounds.find(_.target.origin == tp) match {
          case None => true
          case Some(tpBound) =>
            val implss =
              tpBound.bounds
                .map(_.origin.asInterfaceSymbol)
                .map(_.impls)

            implss.zip(tpBound.bounds).forall {
              case (impls, bound) => impls.exists { impl =>
                lazy val targetSubset = this.isSubsetOf(
                  impl.targetType,
                  thisHpBounds,
                  impl.symbol.hpBound,
                  thatTpBounds,
                  impl.symbol.tpBound
                )

                lazy val interfaceSubset = bound.isSubsetOf(
                  impl.targetInterface,
                  thatHpBounds,
                  impl.symbol.hpBound,
                  thatTpBounds,
                  impl.symbol.tpBound
                )

                targetSubset && interfaceSubset
              }
            }
        }
      }

      def compareBothDiffTPs(tp0: Symbol.TypeParamSymbol, tp1: Symbol.TypeParamSymbol): Boolean = {
        val tpBound0 = thisTpBounds.find(_.target.origin == tp0)
        val tpBound1 = thatTpBounds.find(_.target.origin == tp1)

        (tpBound0, tpBound1) match {
          case (None, None) => true
          case (None, Some(_)) => false
          case (Some(_), None) => true
          case (Some(bound0), Some(bound1)) =>
            val table = bound0.bounds.groupBy(_.origin)

            bound1.bounds.forall { bound =>
              table.get(bound.origin) match {
                case None => false
                case Some(interfaces) => interfaces.exists {
                  _.isSubsetOf(
                    bound,
                    thisHpBounds,
                    thatHpBounds,
                    thisTpBounds,
                    thatTpBounds
                  )
                }
              }
            }
        }
      }

      (this.origin, that.origin) match {
        case (t0: Symbol.EntityTypeSymbol, t1: Symbol.EntityTypeSymbol) => compareBothEntity(t0, t1)
        case (t0: Symbol.EntityTypeSymbol, t1: Symbol.TypeParamSymbol) => compareEntityAndTypeParam(t0, t1)
        case (_: Symbol.TypeParamSymbol, _: Symbol.EntityTypeSymbol) => false
        case (t0: Symbol.TypeParamSymbol, t1: Symbol.TypeParamSymbol) if t0 == t1 => true
        case (t0: Symbol.TypeParamSymbol, t1: Symbol.TypeParamSymbol) => compareBothDiffTPs(t0, t1)

      }
    }

    def isValidForParam(
      that: Type.RefType,
      callerHpBounds: Vector[HPBound],
      calledHpBounds: Vector[HPBound],
      callerTpBounds: Vector[TPBound],
      calledTpBounds: Vector[TPBound],
      hpTable: Map[Symbol.HardwareParamSymbol, HPExpr],
      tpTable: Map[Symbol.TypeParamSymbol, Type.RefType]
    ): Boolean = {
      val replacedThat = that.replaceWithMap(hpTable, tpTable)

      def buildHpTable(origin: Type.RefType, src: Type.RefType): Option[Map[Symbol.HardwareParamSymbol, HPExpr]] = {
        (origin.origin, src.origin) match {
          case (e0: Symbol.EntityTypeSymbol, e1: Symbol.EntityTypeSymbol) if e0 != e1 => None
          case (_: Symbol.EntityTypeSymbol, _: Symbol.EntityTypeSymbol) =>
            val childTable = origin.typeParam
              .zip(src.typeParam)
              .map { case (originTp, srcTp) => buildHpTable(originTp, srcTp) }

            if (childTable.contains(None)) None
            else {
              val children = childTable
                .flatten
                .foldLeft(Map.empty[Symbol.HardwareParamSymbol, HPExpr]) { case (acc, map) => acc ++ map }

              Some(
                children ++
                  origin.hardwareParam
                    .zip(src.hardwareParam)
                    .collect { case (ident: Ident, expr: HPExpr) => ident.symbol.asHardwareParamSymbol -> expr }
                    .toMap
              )
            }
          case (_: Symbol.EntityTypeSymbol, _: Symbol.TypeParamSymbol) => None
          case _ => Some(Map.empty)
        }
      }

      def buildTpTable(origin: Type.RefType, src: Type.RefType): Option[Map[Symbol.TypeParamSymbol, Type.RefType]] = {
        (origin.origin, src.origin) match {
          case (e0: Symbol.EntityTypeSymbol, e1: Symbol.EntityTypeSymbol) if e0 != e1 => None
          case (_: Symbol.EntityTypeSymbol, _: Symbol.EntityTypeSymbol) =>
            val childTable = origin.typeParam
              .zip(src.typeParam)
              .map { case (originTp, srcTp) => buildTpTable(originTp, srcTp) }

            if (childTable.contains(None)) None
            else Some(
              childTable
                .flatten
                .foldLeft(Map.empty[Symbol.TypeParamSymbol, Type.RefType]) {
                  case (acc, map) => acc ++ map
                }
            )
          case (tp: Symbol.TypeParamSymbol, _) => Some(Map(tp -> src))
          case (_: Symbol.EntityTypeSymbol, _: Symbol.TypeParamSymbol) => None
        }
      }

      if (this =!= replacedThat) false
      else {
        lazy val replacedHPBounds = calledHpBounds.map { hpBound =>
          val target = hpBound.target.replaceWithMap(hpTable)
          val bounds = hpBound.bounds.map(_.map(_.replaceWithMap(hpTable)))
          HPBound(target, bounds, hpBound.range)
        }

        lazy val replacedTPBounds = calledTpBounds.map { tpBound =>
          val bounds = tpBound.bounds.map(_.replaceWithMap(hpTable, tpTable))
          TPBound(tpBound.target, bounds)
        }

        lazy val isValidHPs = replacedHPBounds.forall {
          calledBound =>
            callerHpBounds.find(_.target == calledBound.target) match {
              case None => false
              case Some(callerBound) => calledBound.bounds.forall { bound =>
                callerBound.bounds.contains(bound) &&
                  callerBound.range.isSubsetOf(calledBound.range)
              }
            }
        }

        lazy val isValidTPs = replacedTPBounds.forall {
          calledBound => callerTpBounds.find()
        }
      }
    }

    def verification(
      symbol: Symbol with HasParams,
      froms: Vector[Type.RefType],
      toes: Vector[Type.RefType]
    ) = {
      def isValidPair(from: Type.RefType, to: Type.RefType): Boolean = {
        (from.origin, to.origin) match {
          case (e0: Symbol.EntityTypeSymbol, e1: Symbol.EntityTypeSymbol) =>
            if (e0 != e1) false
            else from.typeParam
              .zip(to.typeParam)
              .forall { case (f, t) => isValidPair(f, t) }
          case (_: Symbol.TypeParamSymbol, _: Symbol.EntityTypeSymbol) => false
          case _ => true
        }
      }


      def buildTpTable(
        from: Type.RefType,
        to: Type.RefType,
        table: Map[Symbol.TypeParamSymbol, Option[Type.RefType]]
      ): Map[Symbol.TypeParamSymbol, Option[Type.RefType]] = {
        (from.origin, to.origin) match {
          case (_: Symbol.EntityTypeSymbol, _: Symbol.EntityTypeSymbol) =>
            from.typeParam
              .zip(to.typeParam)
              .foldLeft(table) { case (acc, (from, to)) => buildTpTable(from, to, acc) }
          case (_, tp: Symbol.TypeParamSymbol) =>
            if (table.contains(tp)) table.updated(tp, Some(from))
            else table
          case (_: Symbol.TypeParamSymbol, _: Symbol.EntityTypeSymbol) =>
            table
        }
      }

      def buildHpTable(
        from: Type.RefType,
        to: Type.RefType,
        table: Map[Symbol.HardwareParamSymbol, Option[HPExpr]]
      ): Map[Symbol.HardwareParamSymbol, Option[HPExpr]] = {
        (from.origin, to.origin) match {
          case (_: Symbol.EntityTypeSymbol, _: Symbol.EntityTypeSymbol) =>
            val updatedTable = from.hardwareParam
              .zip(to.hardwareParam)
              .collect { case (expr, ident: Ident) => (expr, ident) }
              .foldLeft(table) {
                case (acc, (from, to)) =>
                  val hpSymbol = to.symbol.asHardwareParamSymbol

                  if (acc.contains(hpSymbol)) acc.updated(hpSymbol, Some(from))
                  else acc
              }

            from.typeParam
              .zip(to.typeParam)
              .foldLeft(updatedTable) {
                case (acc, (f, t)) => buildHpTable(f, t, acc)
              }
          case _ => table
        }
      }

      def unwrap[K, V](table: Map[K, Option[V]]): Either[Error, Map[K, V]] = {
        val (errs, pairs) = table.map {
          case (key, Some(value)) => Right(key -> value)
          case (key, None) => Left(???)
        }.partitionMap(identity)

        if(errs.isEmpty) Right(pairs.toMap)
        else Left(Error.MultipleErrors(errs.toVector))
      }


      val isValid = froms.zip(toes).forall { case (f, t) => isValidPair(f, t) }
      lazy val initTpTable = symbol.typeParam.map(_ -> Option.empty[Type.RefType]).toMap
      lazy val initHpTable = symbol.hardwareParam.map(_ -> Option.empty[HPExpr]).toMap

      if (isValid) None
      else {
        val assignedTpTable = froms.zip(toes).foldLeft(initTpTable){ case (acc, (f, t)) => buildTpTable(f, t, acc) }
        val assignedHpTable = froms.zip(toes).foldLeft(initHpTable){ case (acc, (f, t)) => buildHpTable(f, t, acc) }
        val tpTable = unwrap(assignedTpTable)
        val hpTable = unwrap(assignedHpTable)


      }
    }
    */

    /**
     * This method does not expect that
     * (1)type parameter lengths are mismatch
     * (2)type parameter's type violate type bounds
     * This method expects above violation are treated as [[Type.ErrorType]] already.
     */
      /*
    def <|=(other: Type.RefType): Boolean = {
      (this.origin, other.origin) match {
        case (sym0: Symbol.EntityTypeSymbol, sym1: Symbol.EntityTypeSymbol) =>
          def isSameTP: Boolean = this.typeParam
            .zip(other.typeParam)
            .forall { case (t, o) => t <|= o }

          sym0 == sym1 && isSameTP
        case (_: Symbol.EntityTypeSymbol, sym1: Symbol.TypeParamSymbol) =>
          def isApplicative(impl: ImplementInterfaceContainer, bound: Type.RefType): Boolean =
            (bound <|= impl.targetInterface) && (this <|= impl.targetType)

          val impls = sym1.getBounds
            .map(_.origin.asInterfaceSymbol)
            .map(_.impls)

          sym1.getBounds.zip(impls).view
            .map { case (bound, impls) => impls.filter(isApplicative(_, bound)) }
            .forall(_.nonEmpty)
        case (_: Symbol.TypeParamSymbol, _: Symbol.EntityTypeSymbol) => false
        case (sym0: Symbol.TypeParamSymbol, sym1: Symbol.TypeParamSymbol) =>
          sym1.getBounds.forall {
            rightBound =>
              sym0.getBounds.exists {
                leftBound => leftBound <|= rightBound
              }
          }
      }
    }

    def >|=(other: Type.RefType): Boolean = other <|= this
       */
  }

  object RefType {
    def apply(origin: Symbol.TypeSymbol, hp: Vector[HPExpr], tp: Vector[RefType]): RefType =
      new RefType(origin, hp, tp)

    def apply(origin: Symbol.TypeSymbol): RefType =
      new RefType(origin, Vector.empty, Vector.empty)

    def unapply(arg: Type.RefType): Option[(Symbol.TypeSymbol, Vector[HPExpr], Vector[RefType])] = {
      Some((arg.origin, arg.hardwareParam, arg.typeParam))
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

      if(params.length != args.length) Left(paramMissMatch)
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
            if(e0 != e1) Left(Error.TypeMissMatch(target, caller))
            else {
              val validHPs = caller.hardwareParam
                .zip(target.hardwareParam)
                .forall{ case (c, t) => isHpSuperSet(c, t) }

              val validTPs = caller.typeParam
                .zip(target.typeParam)
                .map{ case (c, t) => verify(c, t) }
                .forall(_.isRight)

              if(validHPs && validTPs) Right(())
              else Left(Error.TypeMissMatch(target, caller))
            }
          case (_, _: Symbol.TypeParamSymbol) => Right(())
          case (_: Symbol.TypeParamSymbol, _) => Left(Error.TypeMissMatch(target, caller))
        }
      }

      val (errs, _) = (caller zip target)
        .map{ case (c, t) => verify(c, t) }
        .partitionMap(identity)

      if(errs.isEmpty) Right(())
      else Left(Error.MultipleErrors(errs: _*))
    }

    def unwrapTable[K, V](table: Map[K, Option[V]]): Either[Error, Map[K, V]] = {
      val (errs, pairs) = table.map {
        case (key, Some(value)) => Right(key -> value)
        case (key, None) => Left(???)
      }.partitionMap(identity)

      if(errs.isEmpty) Right(pairs.toMap)
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

      unwrapTable(assigned)
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

      unwrapTable(assignedTable)
    }

    def verifyHPBounds(
      swapped: Vector[HPBound],
      callerHPBound: Vector[HPBound]
    ): Either[Error, Unit] = {
      val (errs, _) = swapped.map(HPBound.verifyMeetBound(_, callerHPBound)).partitionMap(identity)

      if(errs.isEmpty) Right(())
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
      if(method.params.length != args.length) Left(Error.ParameterLengthMismatch(method.params.length, args.length))
      else {
        val (errs, _) = method.params.zip(args).map {
          case (p, a) if p =:= a => Right(())
          case (p, a) => Left(Error.TypeMissMatch(p, a))
        }.partitionMap(identity)

        if(errs.isEmpty) Right(())
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

  def unitTpe(implicit global: GlobalData): Type.RefType = {
    val symbol = global.builtin.lookup("Unit")
    Type.RefType(symbol)
  }

  def boolTpe(implicit global: GlobalData): Type.RefType = {
    val symbol = global.builtin.lookup("Boolean")
    Type.RefType(symbol)
  }

  def bitTpe(width: IntLiteral)(implicit global: GlobalData): Type.RefType = {
    val symbol = global.builtin.lookup("Bit")
    val IntLiteral(value) = width

    if(value > 0) Type.RefType(symbol, Vector(width), Vector.empty)
    else throw new ImplementationErrorException(s"Bit's width[${value}] must be natural number")
  }

  def numTpe(implicit global: GlobalData): Type.RefType = {
    val symbol = global.builtin.lookup("Num")
    Type.RefType(symbol, Vector.empty, Vector.empty)
  }

  def strTpe(implicit global: GlobalData): Type.RefType = {
    val symbol = global.builtin.lookup("Str")
    Type.RefType(symbol, Vector.empty, Vector.empty)
  }

  def buildType[T <: Symbol.TypeSymbol](typeTree: TypeTree)(implicit ctx: Context.NodeContext, global: GlobalData, ev0: ClassTag[T], ev1: TypeTag[T]): (Option[Error], TypeTree) = {
    val TypeTree(ident: Ident, hps, tps) = typeTree

    ctx.lookup[T](ident.name) match {
      case LookupResult.LookupFailure(err) => (Some(err), typeTree.setSymbol(Symbol.ErrorSymbol).setTpe(Type.ErrorType))
      case LookupResult.LookupSuccess(symbol) =>
        buildParams(hps, tps) match {
          case Left(err) => (Some(err), typeTree.setSymbol(symbol).setTpe(Type.ErrorType))
          case Right((hps, tps)) =>
            val refTpe = Type.RefType(symbol, hps, tps.map(_.tpe.asRefType))
            (None, TypeTree(ident, hps, tps).setSymbol(symbol).setTpe(refTpe).setID(typeTree.id))
        }
    }
  }

  private def buildHP(hp: HPExpr)(implicit ctx: Context.NodeContext, global: GlobalData): (Option[Error], HPExpr) = {
    hp match {
      case lit: IntLiteral => (None, lit.setTpe(Type.numTpe))
      case lit: StringLiteral => (None, lit.setTpe(Type.strTpe))
      case ident@Ident(name) => ctx.lookup[Symbol.HardwareParamSymbol](name) match {
        case LookupResult.LookupFailure(err) => (Some(err), ident.setSymbol(Symbol.ErrorSymbol).setTpe(Type.ErrorType))
        case LookupResult.LookupSuccess(symbol) => (None, ident.setSymbol(symbol).setTpe(symbol.tpe))
      }
      case HPBinOp(op, left, right) =>
        val (err0, builtLeft) = buildHP(left)
        val (err1, builtRight) = buildHP(right)

        val errs0 = Vector(err0, err1).flatten
        val errs1 =
          if (builtLeft.tpe =!= Type.numTpe && builtLeft.tpe =!= Type.ErrorType) errs0 :+ Error.TypeMissMatch(Type.numTpe, builtLeft.tpe)
          else if (builtRight.tpe =!= Type.numTpe && builtLeft.tpe =!= Type.ErrorType) errs0 :+ Error.TypeMissMatch(Type.numTpe, builtRight.tpe)
          else errs0

        val (errs, tpe) =
          if (errs1.isEmpty) (None, Type.numTpe)
          else (Some(Error.MultipleErrors(errs1: _*)), Type.ErrorType)

        (errs, HPBinOp(op, builtLeft, builtRight).setTpe(tpe))
    }
  }

  private def buildParams(hps: Vector[HPExpr], tps: Vector[TypeTree])(implicit ctx: Context.NodeContext, global: GlobalData): Either[Error, (Vector[HPExpr], Vector[TypeTree])] = {
    val (hpErrs, builtHPs) = hps.map(buildHP).unzip
    val (tpErrs, builtTPs) = tps.map(buildType[Symbol.TypeSymbol]).unzip

    val allErrs = hpErrs.flatten ++ tpErrs.flatten

    if (allErrs.isEmpty) Right(builtHPs.map(_.sort), builtTPs)
    else Left(Error.MultipleErrors(allErrs: _*))
  }
}