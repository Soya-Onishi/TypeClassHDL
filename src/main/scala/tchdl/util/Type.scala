package tchdl.util

import tchdl.ast._
import tchdl.typecheck.{ImplementClassContainer, ImplementContainer, ImplementInterfaceContainer, Namer, Typer}
import tchdl.util.Error.MultipleErrors
import tchdl.util.TchdlException.ImplementationErrorException

import scala.collection.mutable
import scala.reflect.ClassTag
import scala.reflect.runtime.universe.TypeTag

trait Type {
  def name: String

  def namespace: NameSpace

  protected def declares: Scope

  def asRefType: Type.RefType = this.asInstanceOf[Type.RefType]

  def asEntityType: Type.EntityType = this.asInstanceOf[Type.EntityType]
  def asParameterType: Type.ParameterType = this.asInstanceOf[Type.ParameterType]
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

  class TypeGenerator(tree: Definition, ctx: Context) extends Type {
    val name = "<?>"

    def declares = throw new TchdlException.ImplementationErrorException("TypeGenerator prohibits an access of 'declares'")
    def namespace = throw new TchdlException.ImplementationErrorException("TypeGenerator prohibits an access of 'namespace'")
    def generate: Type = {
      tree match {
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
        case module: ModuleDef =>
          val paramCtx = Context(ctx, module.symbol)
          val namedHp = module.hp.map(Namer.nodeLevelNamed(_, paramCtx)).map(_.symbol.asHardwareParamSymbol)
          val namedTp = module.tp.map(Namer.nodeLevelNamed(_, paramCtx)).map(_.symbol.asTypeParamSymbol)

          val componentCtx = Context(paramCtx)
          module.components.map(Namer.nodeLevelNamed(_, componentCtx))

          EntityType(module.name, ctx.path, namedHp, namedTp, componentCtx.scope)
        case struct: StructDef =>
          val paramCtx = Context(ctx, struct.symbol)
          val namedHp = struct.hp.map(Namer.nodeLevelNamed(_, paramCtx)).map(_.symbol.asHardwareParamSymbol)
          val namedTp = struct.tp.map(Namer.nodeLevelNamed(_, paramCtx)).map(_.symbol.asTypeParamSymbol)

          val fieldCtx = Context(paramCtx)
          struct.fields.map(Namer.nodeLevelNamed(_, fieldCtx))

          EntityType(struct.name, ctx.path, namedHp, namedTp, fieldCtx.scope)
        case interface: InterfaceDef =>
          val signatureCtx = Context(ctx, interface.symbol)
          val namedHp = interface.hp.map(Namer.nodeLevelNamed(_, signatureCtx)).map(_.symbol.asHardwareParamSymbol)
          val namedTp = interface.tp.map(Namer.nodeLevelNamed(_, signatureCtx)).map(_.symbol.asTypeParamSymbol)

          val interfaceCtx = Context(signatureCtx)
          interface.methods.map(Namer.nodeLevelNamed(_, interfaceCtx))

          EntityType(interface.name, ctx.path, namedHp, namedTp, interfaceCtx.scope)
        case method: MethodDef =>
          val paramCtx = Context(ctx, method.symbol)
          val namedHp = method.hp.map(Namer.nodeLevelNamed(_, paramCtx)).map(_.symbol.asHardwareParamSymbol)
          val namedTp = method.tp.map(Namer.nodeLevelNamed(_, paramCtx)).map(_.symbol.asTypeParamSymbol)
          val paramTpes = method.params
            .map(Namer.nodeLevelNamed(_, paramCtx))
            .map(Typer.typedValDef(_)(paramCtx))
            .map(_.symbol.tpe.asRefType)
          val retTpes = Typer.typedTypeTree(method.retTpe)(paramCtx, acceptPkg = false).tpe.asRefType

          MethodType(paramTpes, retTpes, namedHp, namedTp)
        case vdef: ValDef =>
          val nodeCtx = ctx.asInstanceOf[Context.NodeContext]
          val ValDef(_, _, tpeTree, expr) = vdef

          (tpeTree, expr) match {
            case (None, None) =>
              Reporter.appendError(Error.RequireType)
              Type.ErrorType
            case (None, Some(expr)) =>
              val typedExp = Typer.typedExpr(expr)(nodeCtx)
              typedExp.tpe
            case (Some(tpe), _) =>
              val typedTpe = Typer.typedTypeTree(tpe)(nodeCtx, acceptPkg = false)
              typedTpe.tpe
          }
        case stage: StageDef =>
          val paramCtx = Context(ctx, stage.symbol)
          val typedParams = stage.params
            .map(Namer.nodeLevelNamed(_, paramCtx))
            .map(Typer.typedValDef(_)(paramCtx))

          val typedTpe = Typer.typedTypeTree(stage.retTpe)(paramCtx, acceptPkg = false)

          MethodType(
            typedParams.map(_.symbol.tpe.asRefType),
            typedTpe.tpe.asRefType,
            Vector.empty,
            Vector.empty
          )
        case tpeDef: TypeDef =>
          ParameterType(tpeDef.name, ctx.path)
        case ast =>
          val msg = s"${ast.getClass} is not needed to type generation."
          throw new ImplementationErrorException(msg)
      }
    }

    def =:=(other: Type): Boolean =
      throw new ImplementationErrorException("method =:= should not be called in TypeGenerator")
  }

  object TypeGenerator {
    def apply(tree: Definition, ctx: Context): TypeGenerator = new TypeGenerator(tree, ctx)
  }

  abstract class DeclaredType extends Type {
    def returnType: Type = this
  }

  class EntityType(
    val name: String,
    val namespace: NameSpace,
    val hardwareParam: Vector[Symbol.HardwareParamSymbol],
    val typeParam: Vector[Symbol.TypeParamSymbol],
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
      hardwareParam: Vector[Symbol.HardwareParamSymbol],
      typeParam: Vector[Symbol.TypeParamSymbol],
      declares: Scope
    ): EntityType =
      new EntityType(name, namespace, hardwareParam, typeParam, declares)
  }

  class ParameterType (
    val name: String,
    val namespace: NameSpace,
  ) extends DeclaredType {
    val declares: Scope = Scope.empty

    private var constraints: Vector[Type.RefType] = null
    def appendConstraints(constraints: Vector[Type.RefType]): Unit = {
      if(this.constraints == null)
        this.constraints = constraints
      else
        throw new ImplementationErrorException("constraints is already assigned")
    }

    def getConstraints: Vector[Type.RefType] = {
      if(this.constraints == null)
        throw new ImplementationErrorException("constraints is not assigned yet")
      else
        this.constraints
    }

    override def =:=(other: Type): Boolean = other match {
      case other: ParameterType => this.name == other.name && this.namespace == other.namespace
    }
  }

  object ParameterType {
    def apply(name: String, namespace: NameSpace): ParameterType =
      new ParameterType(name, namespace)
  }

  class MethodType(
    val params: Vector[Type.RefType],
    val returnType: Type.RefType,
    val hardwareParam: Vector[Symbol.HardwareParamSymbol],
    val typeParam: Vector[Symbol.TypeParamSymbol],
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

      MethodType(replacedArgs, replacedRetTpe, this.hardwareParam, this.typeParam)
    }

    def =:=(other: Type): Boolean = other match {
      case other: MethodType =>
        def isSameParam: Boolean = this.params == other.params
        def isSameRet: Boolean = this.returnType == other.returnType
        def isSameHP: Boolean = this.hardwareParam == other.hardwareParam
        def isSameTP: Boolean = this.typeParam == other.typeParam

        isSameParam && isSameRet && isSameHP && isSameTP
    }
  }

  object MethodType {
    def apply(
      args: Vector[Type.RefType],
      retTpe: RefType,
      hp: Vector[Symbol.HardwareParamSymbol],
      tp: Vector[Symbol.TypeParamSymbol]
    ): MethodType =
      new MethodType(args, retTpe, hp, tp)
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

    def lookupMethod2(
      methodName: String,
      typeArgs: Vector[Type.RefType],
      hardArgs: Vector[HPExpr],
      args: Vector[Type.RefType]
    )(implicit ctx: Context): LookupResult[(Symbol.MethodSymbol, Type.MethodType)] = {
      def buildTable[K, V](keys: Vector[K]): Map[K, Option[V]] = keys.map((_, Option.empty[V])).toMap

      def verifyTypeArg(
        method: Symbol.MethodSymbol,
        hpTable: Map[Symbol.HardwareParamSymbol, HPExpr],
        tpTable: Map[Symbol.TypeParamSymbol, Type.RefType]
      ): Either[Error, Unit] = {
        val tps = method.tpe.asMethodType.typeParam
        tps.map {
          tp => tp.getBounds.map(_.replaceWithMap(tpTable))
        }


        val errs =
          methodTpe.typeParam.zip(typeArgs).foldLeft(Vector.empty[Error]) {
            case (errs, (param, arg)) =>
              if(arg <|= Type.RefType(param)) errs
              else errs :+ Error.NotMeetBound(arg, param.getBounds)
          }

        if(errs.isEmpty) Right(())
        else Left(Error.MultipleErrors(errs))
      }

      def verifyHardArg(
        method: Symbol.MethodSymbol,
        hpTable: Map[Symbol.HardwareParamSymbol, HPExpr]
      ): Either[Error, Unit] = {
        val callerBounds = ctx.allHPBounds
        val calledBounds = method.getHPBounds

        HPExpr.verifyHPBound(calledBounds, callerBounds, hpTable)
      }

      def verifyArgTypes(methodTpe: Type.MethodType): Either[Error, Unit] = {
        val (errs, _) = methodTpe.params.zip(args).map {
          case (param, arg) if param =:= arg => Right(())
          case (param, arg) => Left(???)
        }.partitionMap(identity)

        if(errs.isEmpty) Right(())
        else Left(Error.MultipleErrors(errs))
      }

      def unwrap[K, V](table: Map[K, Option[V]]): Either[Error, Map[K, V]] = {
        val (errs, unwrapped) = table.map {
          case (key, Some(value)) => Right(key -> value)
          case (key, None) => Left(???)
        }.partitionMap(identity)

        if(errs.isEmpty) Right(unwrapped.toMap)
        else Left(Error.MultipleErrors(errs.toVector))
      }

      def update[K <: Symbol, V](symbol: K, value: V, table: Map[K, Option[V]]): Map[K, Option[V]] =
        table.get(symbol) match {
          case None => throw new ImplementationErrorException(s"table does not have ${symbol.name} as key")
          case Some(None) => table.updated(symbol, Some(value))
          case Some(_) => table
        }

      def updateMult[K <: Symbol, V](params: Vector[K], args: Vector[V], table: Map[K, Option[V]]): Map[K, Option[V]] =
        params.zip(args).foldLeft(table) {
          case (table, (p, a)) => update(p, a, table)
        }

      def assignHP(param: Type.RefType, arg: Type.RefType)(tab: Map[Symbol.HardwareParamSymbol, Option[HPExpr]]): Map[Symbol.HardwareParamSymbol, Option[HPExpr]] = {
        val table = param.hardwareParam.zip(arg.hardwareParam)
          .foldLeft(tab) {
            case (tab, (paramExpr: Ident, argExpr)) =>
              val hp = paramExpr.symbol.asHardwareParamSymbol
              update(hp, argExpr, tab)
            case (tab, (_, _)) => tab
          }

        assignHPs(param.typeParam, arg.typeParam)(table)
      }

      def assignHPs(params: Vector[Type.RefType], args: Vector[Type.RefType])(tab: Map[Symbol.HardwareParamSymbol, Option[HPExpr]]): Map[Symbol.HardwareParamSymbol, Option[HPExpr]] =
        params.zip(args).foldLeft(tab) {
          case (table, (param, arg)) => assignHP(param, arg)(table)
        }

      def assignTP(param: Type.RefType, arg: Type.RefType)(table: Map[Symbol.TypeParamSymbol, Option[Type.RefType]]): Map[Symbol.TypeParamSymbol, Option[Type.RefType]] =
        param.origin match {
          case tp: Symbol.TypeParamSymbol => update(tp, arg, table)
          case _: Symbol.EntityTypeSymbol => assignTPs(param.typeParam, arg.typeParam)(table)
        }

      def assignTPs(params: Vector[Type.RefType], args: Vector[Type.RefType])(tab: Map[Symbol.TypeParamSymbol, Option[Type.RefType]]): Map[Symbol.TypeParamSymbol, Option[Type.RefType]] =
        params.zip(args).foldLeft(tab) {
          case (table, (param, arg)) => assignTP(param, arg)(table)
        }

      def unwrapTables(
        hpTable: Map[Symbol.HardwareParamSymbol, Option[HPExpr]],
        tpTable: Map[Symbol.TypeParamSymbol, Option[Type.RefType]]
      ): Either[Error, (Map[Symbol.HardwareParamSymbol, HPExpr], Map[Symbol.TypeParamSymbol, Type.RefType])] = {
        (unwrap(hpTable), unwrap(tpTable)) match {
          case (Right(hp), Right(tp)) => Right((hp, tp))
          case (Left(hpErr), Left(tpErr)) => Left(Error.MultipleErrors(hpErr, tpErr))
          case (Left(err), _) => Left(err)
          case (_, Left(err)) => Left(err)
        }
      }

      def verifyLength(methodTpe: Type.MethodType): Either[Error, Unit] = {
        val expects = Vector(
          methodTpe.typeParam.length,
          methodTpe.hardwareParam.length,
          methodTpe.params.length
        )

        val actuals = Vector(
          typeArgs.length,
          hardArgs.length,
          args.length
        )

        val errContainers = Vector(
          Error.TypeParameterLengthMismatch.apply _,
          Error.HardParameterLengthMismatch.apply _,
          Error.ParameterLengthMismatch.apply _
        )

        val errs = (expects, actuals, errContainers).zipped.foldLeft(Vector.empty[Error]) {
          case (errs, (expect, actual, container)) =>
            if(expect == actual) errs
            else errs :+ container(expect, actual)
        }

        if(errs.isEmpty) Right(())
        else Left(Error.MultipleErrors(errs))
      }

      def lookupIntoClassImpl(tpe: Symbol.ClassTypeSymbol): Either[Error, (Symbol.MethodSymbol, Type.MethodType)] = {
        def lookupImpl: Either[Error, ImplementClassContainer] = {
          tpe.lookupImpl(this) match {
            case Vector() => Left(Error.DummyError)
            case Vector(impl) => Right(impl)
            case _ => throw new ImplementationErrorException("multiple impl is detected from one Ref Type")
          }
        }

        for {
          impl <- lookupImpl
          method <- impl.lookup[Symbol.MethodSymbol](methodName).map(Right.apply).getOrElse(Left(Error.DummyError))
          methodTpe = method.tpe.asMethodType
          _ <- verifyLength(methodTpe)
          tpTable0 = buildTable[Symbol.TypeParamSymbol, Type.RefType](impl.typeParam ++ methodTpe.typeParam)
          hpTable0 = buildTable[Symbol.HardwareParamSymbol, HPExpr](impl.hardwareParam ++ methodTpe.hardwareParam)
          tpTable1 = assignTP(impl.targetType, this)(tpTable0)
          hpTable1 = assignHP(impl.targetType, this)(hpTable0)
          tpTable2 = updateMult(methodTpe.typeParam, typeArgs, tpTable1)
          hpTable2 = updateMult(methodTpe.hardwareParam, hardArgs, hpTable1)
          tpTable3 = assignTPs(methodTpe.params, args)(tpTable2)
          hpTable3 = assignHPs(methodTpe.params, args)(hpTable2)
          tables <- unwrapTables(hpTable3, tpTable3)
          (hpTable, tpTable) = tables
          _ <- verifyHardArg(method, hpTable)
          _ <- verifyTypeArg(method, hpTable, tpTable)
          replacedMethodTpe = methodTpe.replaceWithMap(hpTable, tpTable)
          _ <- verifyArgTypes(replacedMethodTpe)
        } yield (method, replacedMethodTpe)
      }

      def lookupIntoInterfaceImpl(): Either[Error, (Symbol.MethodSymbol, Type.MethodType)] = {
        val pairs = for {
          interface <- ctx.interfaceTable.values
          impl <- interface.lookupImpl(this)
          interfaceTpe = interface.tpe
          symbol = interfaceTpe.declares.lookup(methodName)
          methodSymbol <- symbol.collect { case method: Symbol.MethodSymbol => method }
        } yield (impl, methodSymbol)

        val (errs, candidates) = pairs.map {
          case (impl, method) =>
            val implTpTable0 = buildTable(impl.typeParam)
            val implHpTable0 = buildTable(impl.hardwareParam)
            val implTpTable1 = assignTP(impl.targetType, this)(implTpTable0)
            val implHpTable1 = assignHP(impl.targetType, this)(implHpTable0)
            val methodTpe = method.tpe.asMethodType
            val interfaceTpe = impl.targetInterface.origin.tpe.asEntityType

            for {
              _ <- verifyLength(methodTpe)
              implTables <- unwrapTables(implHpTable1, implTpTable1)
              (implHpTable, implTpTable) = implTables
              actualInterface = impl.targetInterface.replaceWithMap(implHpTable, implTpTable)
              tpTable0 = buildTable[Symbol.TypeParamSymbol, Type.RefType](interfaceTpe.typeParam ++ methodTpe.typeParam)
              hpTable0 = buildTable[Symbol.HardwareParamSymbol, HPExpr](interfaceTpe.hardwareParam ++ methodTpe.hardwareParam)
              tpTable1 = updateMult(interfaceTpe.typeParam, actualInterface.typeParam, tpTable0)
              hpTable1 = updateMult(interfaceTpe.hardwareParam, actualInterface.hardwareParam, hpTable0)
              tpTable2 = updateMult(methodTpe.typeParam, typeArgs, tpTable1)
              hpTable2 = updateMult(methodTpe.hardwareParam, hardArgs, hpTable1)
              tpTable3 = assignTPs(methodTpe.params, args)(tpTable2)
              hpTable3 = assignHPs(methodTpe.params, args)(hpTable2)
              tables <- unwrapTables(hpTable3, tpTable3)
              (hpTable, tpTable) = tables
              _ <- verifyHardArg(method, hpTable)
              _ <- verifyTypeArg(method, hpTable, tpTable)
              replacedMethodTpe = methodTpe.replaceWithMap(hpTable, tpTable)
              _ <- verifyArgTypes(replacedMethodTpe)
              methodSymbol = impl
                .lookup[Symbol.MethodSymbol](methodName)
                .getOrElse(throw new ImplementationErrorException(s"$methodName was not found in Implementation"))
            } yield (methodSymbol, replacedMethodTpe)
        }.partitionMap(identity)

        candidates.toVector match {
          case Vector() => Left(Error.MultipleErrors(errs.toVector))
          case Vector(method) => Right(method)
          case methods => Left(Error.AmbiguousSymbols(methods.map(_._1)))
        }
      }

      val methodPair = this.origin match {
        case _: Symbol.TypeParamSymbol =>
          lookupIntoInterfaceImpl()
        case origin: Symbol.ClassTypeSymbol =>
          val res = for {
            _ <- lookupIntoClassImpl(origin).swap
            errs <- lookupIntoInterfaceImpl().swap
          } yield errs

          res.swap
        }

      methodPair match {
        case Right(pair) => LookupResult.LookupSuccess(pair)
        case Left(errs) => LookupResult.LookupFailure(errs)
      }
    }

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
            .forall{ case (t, o) => t.tpe =:= o.tpe}

          isSameLength && isSameType
        }
        def isSameTP = {
          def isSameLength = this.typeParam.length == other.typeParam.length
          def isSameTypes = (this.typeParam zip other.typeParam).forall{ case (t, o) => t =:= o }

          isSameLength && isSameTypes
        }

        isSameOrigin && isSameHpType && isSameTP
    }

    override def equals(obj: Any): Boolean = obj match {
      case other: RefType =>
        def isSameHP = this.hardwareParam == other.hardwareParam

        this =:= other && isSameHP
    }

    /**
     * This method does not expect that
     *   (1)type parameter lengths are mismatch
     *   (2)type parameter's type violate type bounds
     * This method expects above violation are treated as [[Type.ErrorType]] already.
     */
    def <|= (other: Type.RefType): Boolean = {
      (this.origin, other.origin) match {
        case (sym0: Symbol.EntityTypeSymbol, sym1: Symbol.EntityTypeSymbol) =>
          def isSameTP: Boolean = this.typeParam
            .zip(other.typeParam)
            .forall{ case (t, o) => t <|= o }

          sym0 == sym1 && isSameTP
        case (_: Symbol.EntityTypeSymbol, sym1: Symbol.TypeParamSymbol) =>
          def isApplicative(impl: ImplementInterfaceContainer, bound: Type.RefType): Boolean =
            (bound <|= impl.targetInterface) && (this <|= impl.targetType)

          val impls = sym1.getBounds
            .map(_.origin.asInterfaceSymbol)
            .map(_.impls)

          sym1.getBounds.zip(impls).view
            .map{ case (bound, impls) => impls.filter(isApplicative(_, bound)) }
            .forall(_.nonEmpty)
        case (_: Symbol.TypeParamSymbol, _: Symbol.EntityTypeSymbol) => false
        case (sym0: Symbol.TypeParamSymbol, sym1: Symbol.TypeParamSymbol) =>
          sym1.getBounds.forall {
            rightBound => sym0.getBounds.exists {
              leftBound => leftBound <|= rightBound
            }
          }
      }
    }

    def >|=(other: Type.RefType): Boolean = other <|= this
  }

  object RefType {
    def apply(origin: Symbol.TypeSymbol, hp: Vector[HPExpr], tp: Vector[RefType]): RefType =
      new RefType(origin, hp, tp)

    def apply(origin: Symbol.TypeSymbol): RefType =
      new RefType(origin, Vector.empty, Vector.empty)

    def unapply(arg: Type.RefType): Option[(Symbol.TypeSymbol, Vector[HPExpr], Vector[RefType])] = {
      Some((arg.origin, arg.hardwareParam, arg.typeParam))
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

  def unitTpe: Type.RefType = {
    val symbol = Symbol.lookupBuiltin("Unit")
    Type.RefType(symbol)
  }

  def boolTpe: Type.RefType = {
    val symbol = Symbol.lookupBuiltin("Boolean")
    Type.RefType(symbol)
  }

  def bitTpe(width: HPExpr): Type.RefType = {
    val symbol = Symbol.lookupBuiltin("Bit")
    Type.RefType(symbol, Vector(width), Vector.empty)
  }

  def numTpe: Type.RefType = {
    val symbol = Symbol.lookupBuiltin("Num")
    Type.RefType(symbol, Vector.empty, Vector.empty)
  }

  def strTpe: Type.RefType = {
    val symbol = Symbol.lookupBuiltin("Str")
    Type.RefType(symbol, Vector.empty, Vector.empty)
  }

}