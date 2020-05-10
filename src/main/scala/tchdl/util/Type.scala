package tchdl.util

import tchdl.ast._
import tchdl.typecheck.{Namer, Typer}
import tchdl.util.TchdlException.ImplementationErrorException

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
  def =!=(other: Type): Boolean = !(this =:= other)
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
          val namedHp = module.hp.map(Namer.nodeLevelNamed(_, paramCtx)).map(_.symbol.asTermSymbol)
          val namedTp = module.tp.map(Namer.nodeLevelNamed(_, paramCtx)).map(_.symbol.asTypeSymbol)

          val componentCtx = Context(paramCtx)
          module.components.map(Namer.nodeLevelNamed(_, componentCtx))

          EntityType(module.name, ctx.path, namedHp, namedTp, componentCtx.scope)
        case struct: StructDef =>
          val paramCtx = Context(ctx, struct.symbol)
          val namedHp = struct.hp.map(Namer.nodeLevelNamed(_, paramCtx)).map(_.symbol.asTermSymbol)
          val namedTp = struct.tp.map(Namer.nodeLevelNamed(_, paramCtx)).map(_.symbol.asTypeSymbol)

          val fieldCtx = Context(paramCtx)
          struct.fields.map(Namer.nodeLevelNamed(_, fieldCtx))

          EntityType(struct.name, ctx.path, namedHp, namedTp, fieldCtx.scope)
        case interface: InterfaceDef =>
          val signatureCtx = Context(ctx, interface.symbol)
          val namedHp = interface.hp.map(Namer.nodeLevelNamed(_, signatureCtx)).map(_.symbol.asTermSymbol)
          val namedTp = interface.tp.map(Namer.nodeLevelNamed(_, signatureCtx)).map(_.symbol.asTypeSymbol)

          val interfaceCtx = Context(signatureCtx)
          interface.methods.map(Namer.nodeLevelNamed(_, interfaceCtx))

          EntityType(interface.name, ctx.path, namedHp, namedTp, interfaceCtx.scope)
        case method: MethodDef =>
          val paramCtx = Context(ctx, method.symbol)
          val namedHp = method.hp.map(Namer.nodeLevelNamed(_, paramCtx)).map(_.symbol.asTermSymbol)
          val namedTp = method.tp.map(Namer.nodeLevelNamed(_, paramCtx)).map(_.symbol.asTypeSymbol)
          val paramTpes = method.params
            .map(Namer.nodeLevelNamed(_, paramCtx))
            .map(Typer.typedValDef(_)(paramCtx))
            .map(_.symbol.tpe.asRefType)
          val retTpes = Typer.typedTypeAST(method.retTpe)(paramCtx).tpe.asRefType

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
              val typedTpe = Typer.typedTypeAST(tpe)(nodeCtx)
              typedTpe.tpe
          }
        case stage: StageDef =>
          val paramCtx = Context(ctx, stage.symbol)
          val typedParams = stage.params
            .map(Namer.nodeLevelNamed(_, paramCtx))
            .map(Typer.typedValDef(_)(paramCtx))

          val typedTpe = Typer.typedTypeAST(stage.retTpe)(paramCtx)

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
    val hardwareParam: Vector[Symbol.TermSymbol],
    val typeParam: Vector[Symbol.TypeSymbol],
    val declares: Scope
  ) extends DeclaredType {
    import scala.collection.mutable

    class TraitDefPair(val trat: Type.RefType, val tpe: Type.RefType) {
      override def hashCode(): Int = trat.hashCode() + tpe.hashCode()
    }

    private val impls: mutable.Map[Type.RefType, Scope] = mutable.Map[Type.RefType, Scope]()
    def lookupImpl(refTpe: RefType): Option[Scope] = impls.get(refTpe)
    def appendImpl(refTpe: RefType, scope: Scope): Either[Error, Unit] =
      if(impls.contains(refTpe)) Left(Error.ImplementConflict())
      else {
        impls(refTpe) = scope
        Right(())
      }

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
      hardwareParam: Vector[Symbol.TermSymbol],
      typeParam: Vector[Symbol.TypeSymbol],
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
    val params: Vector[RefType],
    val returnType: RefType,
    val hardwareParam: Vector[Symbol.TermSymbol],
    val typeParam: Vector[Symbol.TypeSymbol],
  ) extends Type {
    lazy val name: String = {
      val argTypeNames = params.map(_.name).mkString(", ")
      s"($argTypeNames) -> ${returnType.name}"
    }

    val namespace: NameSpace = NameSpace.empty
    val declares: Scope = returnType.declares

    def replaceWithTypeParamMap(map: Map[Symbol.TypeSymbol, Type.RefType]): Type.MethodType = {
      val replacedArgs = params.map(_.replaceWithTypeParamMap(map))
      val replacedRetTpe = returnType.replaceWithTypeParamMap(map)

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
      args: Vector[RefType],
      retTpe: RefType,
      hp: Vector[Symbol.TermSymbol],
      tp: Vector[Symbol.TypeSymbol]
    ): MethodType =
      new MethodType(args, retTpe, hp, tp)
  }

  class RefType(
    val origin: Symbol.TypeSymbol,
    val hardwareParam: Vector[Expression],
    val typeParam: Vector[RefType]
  ) extends Type {
    val name: String = origin.name
    val namespace: NameSpace = origin.path

    override def declares: Scope = origin.tpe.declares

    def lookupField(name: String): LookupResult = {
      declares.lookup(name) match {
        case Some(symbol) => LookupResult.LookupSuccess(symbol)
        case None => LookupResult.LookupFailure(Error.SymbolNotFound(name))
      }
    }

    def lookupMethod(name: String)(implicit ctx: Context): LookupResult = {
      val implMethod = origin match {
        case origin: Symbol.TypeSymbol with HasImpls => origin.lookupImpl(this) match {
          case Vector() => None
          case Vector(impl) => impl.lookup(name)
          case _ =>
            val msg = "Multiple implementations are detected. However, this case must not be happened due to verifying implementation conflict"
            throw new ImplementationErrorException(msg)
        }
        case symbol => symbol.tpe.declares.lookup(name)
      }

      implMethod match {
        case Some(symbol) => LookupResult.LookupSuccess(symbol)
        case None =>
          // For the case of reference to type parameter
          val symbols = ctx.interfaceTable.values
            .flatMap(_.lookupImpl(this))
            .flatMap(_.lookup(name))
            .filter(_.isMethodSymbol)
            .toVector

          symbols match {
            case Vector(symbol) => LookupResult.LookupSuccess(symbol)
            case Vector() => LookupResult.LookupFailure(Error.SymbolNotFound(name))
            case symbols => LookupResult.LookupFailure(Error.AmbiguousSymbols(symbols))
          }
      }
    }

    // TODO: lookup type that is defined at implementation
    def lookupType(name: String)(implicit ctx: Context): Either[Error, Type] = {
      val tpe = this.origin match {
        case origin: Symbol.EntityTypeSymbol =>origin.lookupImpl(this) match {
          case Vector() => None
          case Vector(impl) => impl.lookup(name)
          case _ =>
            val msg = "Multiple implementations are detected. However, this case must not be happened due to verifying implementation conflict"
            throw new ImplementationErrorException(msg)
        }
        case _ => None
      }

      tpe match {
        case Some(tpe) => tpe.tpe match {
          case Type.ErrorType => Left(Error.DummyError)
          case tpe: Type.RefType => Right(tpe)
        }
        case None =>
          val types = ctx.interfaceTable.values
            .flatMap(_.lookupImpl(this))
            .flatMap(_.lookup(name))
            .collect{ case symbol: Symbol.FieldTypeSymbol => symbol }
            .toVector

          types match {
            case Vector(tpe) => Right(tpe.tpe.asRefType)
            case Vector() => Left(Error.SymbolNotFound(name))
            case types => Left(Error.AmbiguousSymbols(types))
          }
      }
    }

    def replaceWithTypeParamMap(map: Map[Symbol.TypeSymbol, Type.RefType]): Type.RefType =
      map.get(origin) match {
        case Some(tpe) => tpe
        case None =>
          RefType(
            this.origin,
            this.hardwareParam,
            typeParam.map(_.replaceWithTypeParamMap(map))
          )
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
  }

  object RefType {
    def apply(origin: Symbol.TypeSymbol, hp: Vector[Expression], tp: Vector[RefType]): RefType =
      new RefType(origin, hp, tp)

    def apply(origin: Symbol.TypeSymbol): RefType =
      new RefType(origin, Vector.empty, Vector.empty)
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

  def bitTpe(width: Expression): Type.RefType = {
    val symbol = Symbol.lookupBuiltin("Bit")
    Type.RefType(symbol, Vector(width), Vector.empty)
  }
}