package tchdl.typecheck

import tchdl.ast._
import tchdl.util.TchdlException.ImplimentationErrorException
import tchdl.util.{Context, Modifier, Symbol, Type, Visibility}

object Namer {
  def exec(cu: CompilationUnit): (CompilationUnit, Context) = {
    val root = Context.root(cu.pkgName)

    val namedDefs = cu.topDefs.map(named(_, root))
    val namedCu = CompilationUnit(cu.filename, cu.pkgName, namedDefs)

    (namedCu, root)
  }

  def named[T](ast: T, ctx: Context): T = {
    val namedAST = ast match {
      case cu: CompilationUnit =>
        val namedDefs = cu.topDefs.map(named(_, ctx))
        CompilationUnit(cu.filename, cu.pkgName, namedDefs)
      case module: ModuleDef =>
        val tpe = Type.TypeGenerator(module, ctx)
        val symbol: Symbol = Symbol.ModuleSymbol(module.name, ctx.path, Visibility.Public, Modifier.NoModifier, tpe)
        ctx.append(symbol)

        module.setSymbol(symbol)
      case struct: StructDef=>
        val tpe = Type.TypeGenerator(struct, ctx)
        val symbol: Symbol = Symbol.StructSymbol(struct.name, ctx.path, Visibility.Public, Modifier.NoModifier, tpe)
        ctx.append(symbol)

        struct.setSymbol(symbol)
      case always: AlwaysDef =>
        val owner = ctx.owner match {
          case Some(owner: Symbol.ModuleSymbol) =>
            owner
          case Some(_) =>
            throw new ImplimentationErrorException("Module Symbol should be owner, but there is different type owner")
          case None =>
            throw new ImplimentationErrorException("Module Symbol should be owner, but there is no owner")
        }

        val symbol: Symbol = Symbol.AlwaysSymbol(always.name, ctx.path, owner)
        ctx.append(symbol)

        always.setSymbol(symbol)
      case method: MethodDef =>
        val tpe = Type.TypeGenerator(method, ctx)

        val owner = ctx.owner match {
          case Some(owner) => owner
          case None => throw new ImplimentationErrorException("there should be owner, but no one")
        }

        val symbol: Symbol = Symbol.MethodSymbol(
          method.name,
          ctx.path,
          Visibility.Public,
          owner,
          Modifier.NoModifier,
          tpe
        )

        ctx.append(symbol)

        method.setSymbol(symbol)
      case vdef: ValDef =>
        val tpe = Type.TypeGenerator(vdef, ctx)

        val owner = ctx.owner match {
          case Some(owner) => owner
          case None => throw new ImplimentationErrorException("there should be owner, but no one")
        }

        val symbol: Symbol = Symbol.VariableSymbol(
          vdef.name,
          ctx.path,
          Visibility.Public,
          owner,
          Modifier.NoModifier,
          tpe
        )

        ctx.append(symbol)

        vdef.setSymbol(symbol)
      case stage: StageDef =>
        val tpe = Type.TypeGenerator(stage, ctx)

        val owner = ctx.owner match {
          case Some(owner: Symbol.ModuleSymbol) =>
            owner
          case Some(_) =>
            throw new ImplimentationErrorException("Module Symbol should be owner, but there is different type owner")
          case None =>
            throw new ImplimentationErrorException("Module Symbol should be owner, but there is no owner")
        }

        val symbol: Symbol = Symbol.StageSymbol(
          stage.name,
          ctx.path,
          owner,
          tpe
        )

        ctx.append(symbol)

        stage.setSymbol(symbol)
      case state: StateDef =>
        val owner = ctx.owner match {
          case Some(owner: Symbol.StageSymbol) => owner
          case Some(_) =>
            throw new ImplimentationErrorException("Module Symbol should be owner, but there is different type owner")
          case None =>
            throw new ImplimentationErrorException("Module Symbol should be owner, but there is no owner")
        }

        val symbol: Symbol = Symbol.StateSymbol(state.name, ctx.path, owner)
        ctx.append(symbol)

        state.setSymbol(symbol)
      case typeDef: TypeDef =>
        val owner = ctx.owner match {
          case Some(owner) => owner
          case None => throw new ImplimentationErrorException("there should be owner, but no one")
        }

        val tpe = Type.TypeGenerator(typeDef, ctx)
        val symbol: Symbol = Symbol.TypeParamSymbol(typeDef.name, ctx.path, owner, tpe)
        ctx.append(symbol)

        typeDef.setSymbol(symbol)
      case ast => ast
    }

    namedAST.asInstanceOf[T]
  }
}
