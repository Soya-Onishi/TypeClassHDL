package tchdl.util

import tchdl.ast._
import tchdl.typecheck.{Namer, Typer}
import tchdl.util.TchdlException.ImplimentationErrorException

trait Type {
  def name: String

  def namespace: NameSpace

  protected def declares: Scope

  def asRefType: Type.RefType = this.asInstanceOf[Type.RefType]

  def asEntityType: Type.EntityType = this.asInstanceOf[Type.EntityType]
  def asParameterType: Type.ParameterType = this.asInstanceOf[Type.ParameterType]
  def asMethodType: Type.MethodType = this.asInstanceOf[Type.MethodType]

  def isErrorType: Boolean = this.isInstanceOf[Type.ErrorType.type]
}

object Type {

  class TypeGenerator(tree: Definition, ctx: Context) extends Type {
    val name = "<?>"

    def declares = throw new TchdlException.ImplimentationErrorException("TypeGenerator prohibits an access of 'declares'")

    def namespace = throw new TchdlException.ImplimentationErrorException("TypeGenerator prohibits an access of 'namespace'")

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
          val paramCtx = Context(ctx, module.name)
          val namedHp = module.hp.map(Namer.named(_, paramCtx)).map(_.symbol.asTermSymbol)
          val namedTp = module.tp.map(Namer.named(_, paramCtx)).map(_.symbol.asTypeSymbol)

          val componentCtx = Context(paramCtx, module.name)
          module.components.map(Namer.named(_, componentCtx))

          EntityType(module.name, ctx.path, namedHp, namedTp, componentCtx.scope)
        case struct: StructDef =>
          val paramCtx = Context(ctx, struct.name)
          val namedHp = struct.hp.map(Namer.named(_, paramCtx)).map(_.symbol.asTermSymbol)
          val namedTp = struct.tp.map(Namer.named(_, paramCtx)).map(_.symbol.asTypeSymbol)

          val fieldCtx = Context(paramCtx, struct.name)
          struct.fields.map(Namer.named(_, fieldCtx))

          EntityType(struct.name, ctx.path, namedHp, namedTp, fieldCtx.scope)
        case method: MethodDef =>
          val paramCtx = Context(ctx, method.name, method.symbol)
          val namedHp = method.hp.map(Namer.named(_, paramCtx)).map(_.symbol.asTermSymbol)
          val namedTp = method.tp.map(Namer.named(_, paramCtx)).map(_.symbol.asTypeSymbol)
          val paramTpes = method.params
            .map(Namer.named(_, paramCtx))
            .map(Typer.typedValDef(_)(paramCtx))
            .map(_.symbol.tpe.asRefType)
          val retTpes = Typer.typedTypeTree(method.retTpe)(paramCtx).tpe.asRefType

          MethodType(paramTpes, retTpes, namedHp, namedTp)
        case vdef: ValDef =>
          val ValDef(_, _, tpeTree, expr) = vdef

          (tpeTree, expr) match {
            case (None, None) =>
              ctx.appendError(Error.RequireType)
              Type.ErrorType
            case (None, Some(expr)) =>
              val typedExp = Typer.typedExpr(expr)(ctx)
              typedExp.tpe
            case (Some(tpe), _) =>
              val typedTpe = Typer.typedTypeTree(tpe)(ctx)
              typedTpe.tpe
          }
        case stage: StageDef =>
          val paramCtx = Context(ctx, stage.name)
          val typedParams = stage.params
            .map(Namer.named(_, paramCtx))
            .map(Typer.typedValDef(_)(paramCtx))

          val typedTpe = Typer.typedTypeTree(stage.retTpe)(paramCtx)

          MethodType(
            typedParams.map(_.symbol.tpe.asRefType),
            typedTpe.tpe.asRefType,
            Vector.empty,
            Vector.empty
          )
        case tpeDef: TypeDef =>
          ParameterType(tpeDef.name, ctx.path)
      }
    }
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

    private var traits: Vector[TraitDefPair] = Vector.empty
    def hasTraitImpl(trat: Type.RefType, tpe: Type.RefType): Boolean =
      traits.contains(new TraitDefPair(trat, tpe))

    def appendTraitImpl(trat: Type.RefType, tpe: Type.RefType): Either[Error, Unit] = {
      val pair = new TraitDefPair(trat, tpe)
      if(traits.contains(pair)) Left(Error.ImplementConflict())
      else {
        traits = pair +: traits
        Right(())
      }
    }

    def getTraits(tpe: Type.RefType): Vector[Type.RefType] =
      traits.filter(_.tpe == tpe).map(_.trat)
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
        throw new ImplimentationErrorException("constraints is already assigned")
    }

    def getConstraints: Vector[Type.RefType] = {
      if(this.constraints == null)
        throw new ImplimentationErrorException("constraints is not assigned yet")
      else
        this.constraints
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

    def lookup(name: String): Either[Error, Vector[Symbol]] = {
      val field = declares.lookup(name).iterator.toVector
      val method = origin.tpe match {
        case tpe: Type.EntityType =>
          tpe.lookupImpl(this)
            .flatMap(_.lookup(name))
            .iterator
            .toVector
        case _ => Vector.empty
      }

      val traits = origin.tpe match {
        case tpe: Type.EntityType =>
          tpe.getTraits(this)
            .map(_.lookup(name))
            .collect{ case Right(syms) => syms }
            .flatten
      }

      if(field.isEmpty && method.isEmpty && traits.isEmpty)
        Left(Error.SymbolNotFound(name))
      else
        Right(field ++ method ++ traits)
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
  }

  object ErrorType extends Type {
    val name: String = "error type"
    val namespace: NameSpace = NameSpace.empty
    val declares: Scope = Scope.empty
  }

  def unitTpe: Type.RefType = {
    val symbol = Symbol.lookupBuiltin("Unit")
    Type.RefType(symbol)
  }
}