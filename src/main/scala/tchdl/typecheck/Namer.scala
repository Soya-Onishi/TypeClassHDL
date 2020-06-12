package tchdl.typecheck

import tchdl.ast._
import tchdl.util._

object Namer {
  def exec(cu: CompilationUnit)(implicit global: GlobalData): Unit = {
    val packageSymbol = cu.pkgName.foldLeft[Symbol.PackageSymbol](global.rootPackage) {
      case (parent, name) => parent.lookup[Symbol.PackageSymbol](name) match {
        case LookupResult.LookupSuccess(pkg) => pkg
        case LookupResult.LookupFailure(_) =>
          val pkg = Symbol.PackageSymbol(parent, name)
          parent.append(pkg)
          pkg
      }
    }

    val root = Context.root(cu.filename.get, cu.pkgName)
    cu.topDefs.map(topLevelNamed(_)(root, global))
    packageSymbol.appendCtx(cu.filename.get, root)
  }

  def namedAlways(always: AlwaysDef)(implicit ctx: Context.NodeContext, global: GlobalData): AlwaysDef = {
    val symbol = Symbol.AlwaysSymbol(always.name, ctx.path)

    ctx.append(symbol)
    always.setSymbol(symbol)
  }

  def namedMethod(method: MethodDef)(implicit ctx: Context.NodeContext, global: GlobalData): MethodDef = {
    val methodTpe = Type.MethodTypeGenerator(method, ctx, global)
    val methodSymbol = Symbol.MethodSymbol(
      method.name,
      ctx.path,
      Visibility.Public,
      Modifier.NoModifier,
      methodTpe
    )

    val signatureCtx = Context(ctx, methodSymbol)
    val namedHPs = method.hp.map(namedHPDef(_)(signatureCtx, global))
    val namedTPs = method.tp.map(namedTPDef(_)(signatureCtx, global))
    methodSymbol.setHPs(namedHPs.map(_.symbol.asHardwareParamSymbol))
    methodSymbol.setTPs(namedTPs.map(_.symbol.asTypeParamSymbol))

    ctx.append(methodSymbol)
    method.setSymbol(methodSymbol)
  }

  def namedValDef(vdef: ValDef)(implicit ctx: Context.NodeContext, global: GlobalData): ValDef = {
    val symbol = Symbol.VariableSymbol(
      vdef.name,
      ctx.path,
      Visibility.Private,
      Modifier.NoModifier,
      Type.VariableTypeGenerator(vdef, ctx, global)
    )

    ctx.append(symbol)
    vdef.setSymbol(symbol)
  }

  def namedHPDef(vdef: ValDef)(implicit ctx: Context.NodeContext, global: GlobalData): ValDef = {
    val symbol = Symbol.HardwareParamSymbol(
      vdef.name,
      ctx.path,
      Type.HPTypeGenerator(vdef, ctx, global)
    )

    ctx.append(symbol)
    vdef.setSymbol(symbol)
  }

  def namedStageDef(stage: StageDef)(implicit ctx: Context.NodeContext, global: GlobalData): StageDef = {
    val symbol = Symbol.StageSymbol(
      stage.name,
      ctx.path,
      Type.StageTypeGenerator(stage, ctx, global)
    )

    ctx.append(symbol)
    stage.setSymbol(symbol)
  }

  def namedStateDef(state: StateDef)(implicit ctx: Context.NodeContext, global: GlobalData): StateDef = {
    val symbol = Symbol.StateSymbol(state.name, ctx.path)

    ctx.append(symbol)
    state.setSymbol(symbol)
  }

  def namedTPDef(typeDef: TypeDef)(implicit ctx: Context.NodeContext, global: GlobalData): TypeDef = {
    val tpe = Type.TypeParamType(typeDef.name, ctx.path)
    val symbol: Symbol = Symbol.TypeParamSymbol(typeDef.name, ctx.path, tpe)

    ctx.append(symbol)
    typeDef.setSymbol(symbol)
  }

  def namedModule(module: ModuleDef)(implicit ctx: Context.RootContext, global: GlobalData): ModuleDef = {
    val moduleTpe = Type.ModuleTypeGenerator(module, ctx, global)
    val moduleSymbol = Symbol.ModuleSymbol(
      module.name,
      ctx.path,
      Visibility.Public,
      Modifier.NoModifier,
      moduleTpe
    )

    val signatureCtx = Context(ctx, moduleSymbol)
    val hps = module.hp.map(namedHPDef(_)(signatureCtx, global))
    val tps = module.tp.map(namedTPDef(_)(signatureCtx, global))
    moduleSymbol.setHPs(hps.map(_.symbol.asHardwareParamSymbol))
    moduleSymbol.setTPs(tps.map(_.symbol.asTypeParamSymbol))

    ctx.append(moduleSymbol)
    module.setSymbol(moduleSymbol)
  }

  def namedStruct(struct: StructDef)(implicit ctx: Context.RootContext, global: GlobalData): StructDef = {
    def tryAppendBuiltIn(symbol: Symbol.StructSymbol): Unit = {
      if(ctx.path.pkgName == Vector("std", "types") && global.builtin.names.contains(struct.name))
        global.builtin.append(symbol)
    }

    val structTpe = Type.StructTypeGenerator(struct, ctx, global)
    val structSymbol = Symbol.StructSymbol(
      struct.name,
      ctx.path,
      Visibility.Public,
      Modifier.NoModifier,
      structTpe
    )

    val signatureCtx = Context(ctx, structSymbol)
    val hps = struct.hp.map(namedHPDef(_)(signatureCtx, global))
    val tps = struct.tp.map(namedTPDef(_)(signatureCtx, global))
    structSymbol.setHPs(hps.map(_.symbol.asHardwareParamSymbol))
    structSymbol.setTPs(tps.map(_.symbol.asTypeParamSymbol))

    tryAppendBuiltIn(structSymbol)
    ctx.append(structSymbol)
    struct.setSymbol(structSymbol)
  }

  def namedInterface(interface: InterfaceDef)(implicit ctx: Context.RootContext, global: GlobalData): InterfaceDef = {
    val interfaceTpe = Type.InterfaceTypeGenerator(interface, ctx, global)
    val interfaceSymbol = Symbol.InterfaceSymbol(
      interface.name,
      ctx.path,
      Visibility.Public,
      Modifier.NoModifier,
      interfaceTpe
    )

    val signatureCtx = Context(ctx, interfaceSymbol)
    val hps = interface.hp.view.map(namedHPDef(_)(signatureCtx, global)).map(_.symbol.asHardwareParamSymbol).to(Vector)
    val tps = interface.tp.view.map(namedTPDef(_)(signatureCtx, global)).map(_.symbol.asTypeParamSymbol).to(Vector)
    interfaceSymbol.setHPs(hps)
    interfaceSymbol.setTPs(tps)

    ctx.append(interfaceSymbol)
    interface.setSymbol(interfaceSymbol)
  }

  def namedImplInterface(impl: ImplementInterface)(implicit ctx: Context.RootContext, global: GlobalData): ImplementInterface = {
    val implSymbol = Symbol.ImplementSymbol(impl.id, ctx.path)
    val signatureCtx = Context(ctx, implSymbol)
    val hps = impl.hp.view.map(namedHPDef(_)(signatureCtx, global)).map(_.symbol.asHardwareParamSymbol).to(Vector)
    val tps = impl.tp.view.map(namedTPDef(_)(signatureCtx, global)).map(_.symbol.asTypeParamSymbol).to(Vector)
    implSymbol.setHPs(hps)
    implSymbol.setTPs(tps)

    impl.setSymbol(implSymbol)
  }

  def namedImplClass(impl: ImplementClass)(implicit ctx: Context.RootContext, global: GlobalData): ImplementClass = {
    val implSymbol = Symbol.ImplementSymbol(impl.id, ctx.path)
    val signatureCtx = Context(ctx, implSymbol)
    val hps = impl.hp.view.map(namedHPDef(_)(signatureCtx, global)).map(_.symbol.asHardwareParamSymbol).to(Vector)
    val tps = impl.tp.view.map(namedTPDef(_)(signatureCtx, global)).map(_.symbol.asTypeParamSymbol).to(Vector)
    implSymbol.setHPs(hps)
    implSymbol.setTPs(tps)

    impl.setSymbol(implSymbol)
  }

  def nodeLevelNamed[T](ast: T)(implicit ctx: Context.NodeContext, global: GlobalData): T = {
    val namedTree = ast match {
      case always: AlwaysDef => namedAlways(always)
      case method: MethodDef => namedMethod(method)
      case vdef: ValDef => namedValDef(vdef)
      case stage: StageDef => namedStageDef(stage)
      case state: StateDef => namedStateDef(state)
      case typeDef: TypeDef => namedTPDef(typeDef)
      case ast => ast
    }

    namedTree.asInstanceOf[T]
  }

  def topLevelNamed[T](ast: T)(implicit ctx: Context.RootContext, global: GlobalData): T = {
    val namedAST = ast match {
      case module: ModuleDef => namedModule(module)
      case struct: StructDef=> namedStruct(struct)
      case interface: InterfaceDef => namedInterface(interface)
      case impl: ImplementInterface => namedImplInterface(impl)
      case impl: ImplementClass => namedImplClass(impl)
      case ast => ast
    }

    namedAST.asInstanceOf[T]
  }
}
