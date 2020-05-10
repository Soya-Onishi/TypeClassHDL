package tchdl.typecheck

import tchdl.ast._
import tchdl.util.TchdlException.ImplementationErrorException
import tchdl.util.{Context, Modifier, Symbol, Type, Visibility, PackageRoot, PackageNode}

object Namer {
  def exec(cu: CompilationUnit): Unit = {
    val root = Context.root(cu.pkgName)

    cu.topDefs.map(topLevelNamed(_, root))

    val packageNode = cu.pkgName.foldLeft[PackageNode](PackageRoot) {
      case (node, name) => node.getNode(name) match {
        case Some(pkg) => pkg
        case None =>
          val pkg = PackageNode(name)
          node.appendNode(pkg)
          pkg
      }
    }

    packageNode.appendContext(cu.filename.get, root)
  }

  def nodeLevelNamed[T](ast: T, ctx: Context.NodeContext): T = {
    val namedTree = ast match {
      case always: AlwaysDef =>
        val owner = ctx.owner match {
          case owner: Symbol.ModuleSymbol => owner
          case _ =>
            throw new ImplementationErrorException("Module Symbol should be owner, but there is different type owner")
        }

        val symbol: Symbol = Symbol.AlwaysSymbol(always.name, ctx.path, owner)
        ctx.append(symbol)

        always.setSymbol(symbol)
      case method: MethodDef =>
        val tpe = Type.TypeGenerator(method, ctx)

        val symbol: Symbol = Symbol.MethodSymbol(
          method.name,
          ctx.path,
          Visibility.Public,
          ctx.owner,
          Modifier.NoModifier,
          tpe
        )

        ctx.append(symbol)

        method.setSymbol(symbol)
      case vdef: ValDef =>
        val tpe = Type.TypeGenerator(vdef, ctx)

        val symbol: Symbol = Symbol.VariableSymbol(
          vdef.name,
          ctx.path,
          Visibility.Public,
          ctx.owner,
          Modifier.NoModifier,
          tpe
        )

        ctx.append(symbol)

        vdef.setSymbol(symbol)
      case stage: StageDef =>
        val tpe = Type.TypeGenerator(stage, ctx)

        val owner = ctx.owner match {
          case owner: Symbol.ModuleSymbol => owner
          case _ =>
            throw new ImplementationErrorException("Module Symbol should be owner, but there is different type owner")
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
          case owner: Symbol.StageSymbol => owner
          case _ =>
            throw new ImplementationErrorException("Module Symbol should be owner, but there is no owner")
        }

        val symbol: Symbol = Symbol.StateSymbol(state.name, ctx.path, owner)
        ctx.append(symbol)

        state.setSymbol(symbol)
      case typeDef: TypeDef =>
        val tpe = Type.TypeGenerator(typeDef, ctx)
        val symbol: Symbol = Symbol.TypeParamSymbol(typeDef.name, ctx.path, ctx.owner, tpe)
        ctx.append(symbol)

        typeDef.setSymbol(symbol)
      case ast => ast
    }

    namedTree.asInstanceOf[T]
  }


  def topLevelNamed[T](ast: T, ctx: Context.RootContext): T = {
    val namedAST = ast match {
      case cu: CompilationUnit =>
        val namedDefs = cu.topDefs.map(topLevelNamed(_, ctx))
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
      case interface: InterfaceDef =>
        val tpe = Type.TypeGenerator(interface, ctx)
        val symbol = Symbol.InterfaceSymbol(interface.name, ctx.path, Visibility.Public, Modifier.NoModifier, tpe)
        ctx.append(symbol)

        interface.setSymbol(symbol)
      case impl: ImplementInterface =>
        val symbol = Symbol.ImplementSymbol(impl.id, ctx.path)

        impl.setSymbol(symbol)
      case impl: ImplementClass =>
        val symbol = Symbol.ImplementSymbol(impl.id, ctx.path)

        impl.setSymbol(symbol)
      case ast => ast
    }

    namedAST.asInstanceOf[T]
  }
}
