package tchdl.typecheck

import tchdl.ast._
import tchdl.util.{Context, LookupResult, Modifier, Symbol, Type, Visibility}

object Namer {
  def exec(cu: CompilationUnit): Unit = {
    val packageSymbol = cu.pkgName.foldLeft[Symbol.PackageSymbol](Symbol.RootPackageSymbol) {
      case (parent, name) => parent.lookup[Symbol.PackageSymbol](name) match {
        case LookupResult.LookupSuccess(pkg) => pkg
        case LookupResult.LookupFailure(_) =>
          val pkg = Symbol.PackageSymbol(parent, name)
          parent.append(pkg)
          pkg
      }
    }

    val root = Context.root(cu.filename.get, cu.pkgName)
    cu.topDefs.map(topLevelNamed(_, root))
    packageSymbol.appendCtx(cu.filename.get, root)
  }

  def namedAlways(always: AlwaysDef, ctx: Context.NodeContext): AlwaysDef = {
    val symbol = Symbol.AlwaysSymbol(always.name, ctx.path)

    ctx.append(symbol)
    always.setSymbol(symbol)
  }

  def namedMethod(method: MethodDef, ctx: Context.NodeContext): MethodDef = {
    val methodTpe = Type.MethodTypeGenerator(method, ctx)
    val methodSymbol = Symbol.MethodSymbol(
      method.name,
      ctx.path,
      Visibility.Public,
      Modifier.NoModifier,
      methodTpe
    )

    val signatureCtx = Context(ctx, methodSymbol)
    val namedHPs = method.hp.map(namedHPDef(_, signatureCtx))
    val namedTPs = method.tp.map(namedTPDef(_, signatureCtx))
    methodSymbol.setHPs(namedHPs.map(_.symbol.asHardwareParamSymbol))
    methodSymbol.setTPs(namedTPs.map(_.symbol.asTypeParamSymbol))

    ctx.append(methodSymbol)
    method.setSymbol(methodSymbol)
  }

  def namedValDef(vdef: ValDef, ctx: Context.NodeContext): ValDef = {
    val symbol = Symbol.VariableSymbol(
      vdef.name,
      ctx.path,
      Visibility.Private,
      Modifier.NoModifier,
      Type.VariableTypeGenerator(vdef, ctx)
    )

    ctx.append(symbol)
    vdef.setSymbol(symbol)
  }

  def namedHPDef(vdef: ValDef, ctx: Context.NodeContext): ValDef = {
    val symbol = Symbol.HardwareParamSymbol(
      vdef.name,
      ctx.path,
      Type.VariableTypeGenerator(vdef, ctx)
    )

    ctx.append(symbol)
    vdef.setSymbol(symbol)
  }

  def namedStageDef(stage: StageDef, ctx: Context.NodeContext): StageDef = {
    val symbol = Symbol.StageSymbol(
      stage.name,
      ctx.path,
      Type.StageTypeGenerator(stage, ctx)
    )

    ctx.append(symbol)
    stage.setSymbol(symbol)
  }

  def namedStateDef(state: StateDef, ctx: Context.NodeContext): StateDef = {
    val symbol = Symbol.StateSymbol(state.name, ctx.path)

    ctx.append(symbol)
    state.setSymbol(symbol)
  }

  def namedTPDef(typeDef: TypeDef, ctx: Context.NodeContext): TypeDef = {
    val tpe = Type.TypeParamType(typeDef.name, ctx.path)
    val symbol: Symbol = Symbol.TypeParamSymbol(typeDef.name, ctx.path, tpe)

    ctx.append(symbol)
    typeDef.setSymbol(symbol)
  }

  def namedModule(module: ModuleDef, ctx: Context.RootContext): ModuleDef = {
    val moduleTpe = Type.ModuleTypeGenerator(module, ctx)
    val moduleSymbol = Symbol.ModuleSymbol(
      module.name,
      ctx.path,
      Visibility.Public,
      Modifier.NoModifier,
      moduleTpe
    )

    val signatureCtx = Context(ctx, moduleSymbol)
    val hps = module.hp.map(namedHPDef(_, signatureCtx))
    val tps = module.tp.map(namedTPDef(_, signatureCtx))
    moduleSymbol.setHPs(hps.map(_.symbol.asHardwareParamSymbol))
    moduleSymbol.setTPs(tps.map(_.symbol.asTypeParamSymbol))

    ctx.append(moduleSymbol)
    module.setSymbol(moduleSymbol)
  }

  def namedStruct(struct: StructDef, ctx: Context.RootContext): StructDef = {
    def tryAppendBuiltIn(symbol: Symbol.StructSymbol): Unit = {
      if(ctx.path.pkgName == Vector("std", "types") && Symbol.builtInNames.contains(struct.name)) {
        Symbol.appendBuiltin(symbol)
      }
    }

    val structTpe = Type.StructTypeGenerator(struct, ctx)
    val structSymbol = Symbol.StructSymbol(
      struct.name,
      ctx.path,
      Visibility.Public,
      Modifier.NoModifier,
      structTpe
    )

    val signatureCtx = Context(ctx, structSymbol)
    val hps = struct.hp.map(namedHPDef(_, signatureCtx))
    val tps = struct.tp.map(namedTPDef(_, signatureCtx))
    structSymbol.setHPs(hps.map(_.symbol.asHardwareParamSymbol))
    structSymbol.setTPs(tps.map(_.symbol.asTypeParamSymbol))

    tryAppendBuiltIn(structSymbol)
    ctx.append(structSymbol)
    struct.setSymbol(structSymbol)
  }

  def namedInterface(interface: InterfaceDef, ctx: Context.RootContext): InterfaceDef = {
    val interfaceTpe = Type.InterfaceTypeGenerator(interface, ctx)
    val interfaceSymbol = Symbol.InterfaceSymbol(
      interface.name,
      ctx.path,
      Visibility.Public,
      Modifier.NoModifier,
      interfaceTpe
    )

    val signatureCtx = Context(ctx, interfaceSymbol)
    val hps = interface.hp.view.map(namedHPDef(_, signatureCtx)).map(_.symbol.asHardwareParamSymbol).to(Vector)
    val tps = interface.tp.view.map(namedTPDef(_, signatureCtx)).map(_.symbol.asTypeParamSymbol).to(Vector)
    interfaceSymbol.setHPs(hps)
    interfaceSymbol.setTPs(tps)

    ctx.append(interfaceSymbol)
    interface.setSymbol(interfaceSymbol)
  }

  def namedImplInterface(impl: ImplementInterface, ctx: Context.RootContext): ImplementInterface = {
    val implSymbol = Symbol.ImplementSymbol(impl.id, ctx.path)
    val signatureCtx = Context(ctx, implSymbol)
    val hps = impl.hp.view.map(namedHPDef(_, signatureCtx)).map(_.symbol.asHardwareParamSymbol).to(Vector)
    val tps = impl.tp.view.map(namedTPDef(_, signatureCtx)).map(_.symbol.asTypeParamSymbol).to(Vector)
    implSymbol.setHPs(hps)
    implSymbol.setTPs(tps)

    impl.setSymbol(implSymbol)
  }

  def namedImplClass(impl: ImplementClass, ctx: Context.RootContext): ImplementClass = {
    val implSymbol = Symbol.ImplementSymbol(impl.id, ctx.path)
    val signatureCtx = Context(ctx, implSymbol)
    val hps = impl.hp.view.map(namedHPDef(_, signatureCtx)).map(_.symbol.asHardwareParamSymbol).to(Vector)
    val tps = impl.tp.view.map(namedTPDef(_, signatureCtx)).map(_.symbol.asTypeParamSymbol).to(Vector)
    implSymbol.setHPs(hps)
    implSymbol.setTPs(tps)

    impl.setSymbol(implSymbol)
  }

  def nodeLevelNamed[T](ast: T, ctx: Context.NodeContext): T = {
    val namedTree = ast match {
      case always: AlwaysDef => namedAlways(always, ctx)
      case method: MethodDef => namedMethod(method, ctx)
      case vdef: ValDef => namedValDef(vdef, ctx)
      case stage: StageDef => namedStageDef(stage, ctx)
      case state: StateDef => namedStateDef(state, ctx)
      case typeDef: TypeDef => namedTPDef(typeDef, ctx)
      case ast => ast
    }

    namedTree.asInstanceOf[T]
  }

  def topLevelNamed[T](ast: T, ctx: Context.RootContext): T = {
    val namedAST = ast match {
      case module: ModuleDef => namedModule(module, ctx)
      case struct: StructDef=> namedStruct(struct, ctx)
      case interface: InterfaceDef => namedInterface(interface, ctx)
      case impl: ImplementInterface => namedImplInterface(impl, ctx)
      case impl: ImplementClass => namedImplClass(impl, ctx)
      case ast => ast
    }

    namedAST.asInstanceOf[T]
  }
}
