package tchdl.util

import tchdl.ast._
import tchdl.typecheck.Namer

trait Type {
  def name: String
  def namespace: NameSpace
  def declares: Scope

  def asRefType: Type.RefType = this.asInstanceOf[Type.RefType]
}

object Type {
  class TypeGenerator(tree: Definition, ctx: Context) extends Type {
    val name = "<?>"
    def declares = throw new TchdlException.ImplimentationErrorException("TypeGenerator prohibits an access of 'declares'")
    def namespace = throw new TchdlException.ImplimentationErrorException("TypeGenerator prohibits an access of 'namespace'")

    def generate(): Type = tree match {
      case module: ModuleDef =>
        val paramCtx = Context(ctx, module.name)
        val namedHp = module.hp.map(Namer.named(_, paramCtx)).map(_.symbol.asTermSymbol)
        val namedTp = module.tp.map(Namer.named(_, paramCtx)).map(_.symbol.asTypeSymbol)

        // TODO: Need Typer for hp and tp

        val componentCtx = Context(paramCtx, module.name)
        module.components.map(Namer.named(_, componentCtx))

        // TODO: Need Typer for components

        DeclaredType(module.name, ctx.namespace, namedHp, namedTp, componentCtx.scope)
      case struct: StructDef =>
        val paramCtx = Context(ctx, struct.name)
        val namedHp = struct.hp.map(Namer.named(_, paramCtx)).map(_.symbol.asTermSymbol)
        val namedTp = struct.tp.map(Namer.named(_, paramCtx)).map(_.symbol.asTypeSymbol)

        // TODO: Need Typer for hp and tp

        val fieldCtx = Context(paramCtx, struct.name)
        struct.fields.map(Namer.named(_, fieldCtx))

        // TODO: Need Typer for fields

        DeclaredType(struct.name, ctx.namespace, namedHp, namedTp, fieldCtx.scope)
      case method: MethodDef =>
        val paramCtx = Context(ctx, method.name)
        val namedHp = method.hp.map(Namer.named(_, paramCtx)).map(_.symbol.asTermSymbol)
        val namedTp = method.tp.map(Namer.named(_, paramCtx)).map(_.symbol.asTypeSymbol)
        val namedParam = method.params
          .map(Namer.named(_, paramCtx))
          .map(_.symbol.asTermSymbol)

        /* TODO: Need Typer for hp, tp, parameter and ret type.
         *       If there is no ret type, need to analyze method's expression.
         *       Or, write return type in force for user
         *       (i.e. if there is no ret type explicitly, it is error)
         */


        ???
      case vdef: ValDef =>
        val ValDef(_, _, tpeTree, expr) = vdef

        (tpeTree, expr) match {
          case (None, None) => ??? // TODO: append error that represents there is no type and expression
          case (None, Some(expr)) => ??? // TODO: Need Typer for expr
          case (Some(tpe), _) => ??? // TODO: Need Typer for tpe
        }
      case stage: StageDef =>
        val paramCtx = Context(ctx, stage.name)
        val namedParams = stage.params.map(Namer.named(_, paramCtx)).map(_.symbol.asTermSymbol)

        // TODO: Need Typer for parameters and return types

        ???
    }
  }

  object TypeGenerator {
    def apply(tree: Definition, ctx: Context): TypeGenerator = new TypeGenerator(tree, ctx)
  }

  class DeclaredType(
    val name: String,
    val namespace: NameSpace,
    val hardwareParam: Vector[Symbol.TermSymbol],
    val typeParam: Vector[Symbol.TypeSymbol],
    val declares: Scope,
  ) extends Type {
    def returnType: Type = this
  }

  object DeclaredType {
    def apply(
               name: String,
               namespace: NameSpace,
               hp: Vector[Symbol.TermSymbol],
               tp: Vector[Symbol.TypeSymbol],
               declares: Scope
             ): DeclaredType =
      new DeclaredType(name, namespace, hp, tp, declares)

  }

  class MethodType(
    val args: Vector[RefType],
    val returnType: RefType,
    val hardwareParam: Vector[Symbol.TermSymbol],
    val typeParam: Vector[Symbol.TypeSymbol],
  ) extends Type {
    lazy val name: String = {
      val argTypeNames = args.map(_.name).mkString(", ")
      s"($argTypeNames) -> ${returnType.name}"
    }

    val namespace: NameSpace = NameSpace.empty
    val declares: Scope = returnType.declares
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
    val namespace: NameSpace = origin.namespace
    val declares: Scope = origin.tpe.declares
  }

  object RefType {
    def apply(origin: Symbol.TypeSymbol, hp: Vector[Expression], tp: Vector[RefType]): RefType =
      new RefType(origin, hp, tp)
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
}