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

    val root = Context.root(cu.pkgName)
    cu.topDefs.map(topLevelNamed(_)(root, global))
    packageSymbol.appendCtx(cu.filename, root)
  }

  def namedAlways(always: AlwaysDef)(implicit ctx: Context.NodeContext, global: GlobalData): AlwaysDef = {
    val symbol = Symbol.AlwaysSymbol(always.name, ctx.path)

    ctx.append(symbol).left.foreach(global.repo.error.append)
    always.setSymbol(symbol)
  }

  def namedMethod(method: MethodDef)(implicit ctx: Context, global: GlobalData): MethodDef = {
    def tryAppendOperator(symbol: Symbol.MethodSymbol): Unit = {
      val isTopLevel = ctx.path.pkgName == Vector("std", "functions")
      val hasName = global.builtin.operators.names.contains(symbol.name)

      if(isTopLevel && hasName)
        global.builtin.operators.append(symbol)
    }

    val methodTpe = Type.MethodTypeGenerator(method, ctx, global)
    val methodSymbol = Symbol.MethodSymbol(
      method.name,
      ctx.path,
      Accessibility.Public,
      method.flag,
      methodTpe,
      method.annons
    )

    val signatureCtx = Context(ctx, methodSymbol)
    val namedHPs = method.hp.map(namedHPDef(_)(signatureCtx, global))
    val namedTPs = method.tp.map(namedTypeParamDef(_)(signatureCtx, global))

    methodSymbol.setHPs(namedHPs.map(_.symbol.asHardwareParamSymbol))
    methodSymbol.setTPs(namedTPs.map(_.symbol.asTypeParamSymbol))

    tryAppendOperator(methodSymbol)
    ctx.append(methodSymbol).left.foreach(global.repo.error.append)
    method.setSymbol(methodSymbol)
  }

  def namedFieldDef(vdef: ValDef)(implicit ctx: Context.NodeContext, global: GlobalData): ValDef = {
    val symbol = Symbol.VariableSymbol.field(
      vdef.name,
      ctx.path,
      Accessibility.Private,
      vdef.flag,
      Type.VariableTypeGenerator(vdef, ctx, global)
    )

    ctx.append(symbol).left.foreach(global.repo.error.append)
    vdef.setSymbol(symbol)
  }

  def namedLocalDef(vdef: ValDef)(implicit ctx: Context.NodeContext, global: GlobalData): ValDef = {
    val symbol = Symbol.VariableSymbol.local(
      vdef.name,
      ctx.path,
      Accessibility.Private,
      vdef.flag,
      Type.VariableTypeGenerator(vdef, ctx, global)
    )

    ctx.append(symbol).left.foreach(global.repo.error.append)
    vdef.setSymbol(symbol)
  }

  def namedEnumMember(member: EnumMemberDef)(implicit ctx: Context.NodeContext, global: GlobalData): EnumMemberDef = {
    val generator = Type.EnumMemberTypeGenerator(member, ctx, global)
    val symbol = Symbol.EnumMemberSymbol(member.name, ctx.path, generator)

    ctx.append(symbol).left.foreach(global.repo.error.append)
    member.setSymbol(symbol)
  }

  def namedHPDef(vdef: ValDef)(implicit ctx: Context.NodeContext, global: GlobalData): ValDef = {
    val symbol = Symbol.HardwareParamSymbol(
      vdef.name,
      ctx.path,
      Type.HPTypeGenerator(vdef, ctx, global)
    )

    ctx.append(symbol).left.foreach(global.repo.error.append)
    vdef.setSymbol(symbol)
  }

  def namedStageDef(stage: StageDef)(implicit ctx: Context.NodeContext, global: GlobalData): StageDef = {
    val symbol = Symbol.StageSymbol(
      stage.name,
      ctx.path,
      Type.StageTypeGenerator(stage, ctx, global)
    )

    ctx.append(symbol).left.foreach(global.repo.error.append)
    stage.setSymbol(symbol)
  }

  def namedStateDef(state: StateDef)(implicit ctx: Context.NodeContext, global: GlobalData): StateDef = {
    val symbol = Symbol.StateSymbol(state.name, ctx.path, Type.StateTypeGenerator(state, ctx, global))

    ctx.append(symbol).left.foreach(global.repo.error.append)
    state.setSymbol(symbol)
  }

  def namedTypeParamDef(typeDef: TypeDef)(implicit ctx: Context.NodeContext, global: GlobalData): TypeDef = {
    val tpe = Type.TypeParamType(typeDef.name, ctx.path)
    val symbol: Symbol = Symbol.TypeParamSymbol(typeDef.name, ctx.path, tpe)

    ctx.append(symbol).left.foreach(global.repo.error.append)
    typeDef.setSymbol(symbol)
  }

  def namedFieldTypeDef(typeDef: TypeDef)(implicit ctx: Context.NodeContext, global: GlobalData): TypeDef = {
    val tpe = Type.FieldTypeGenerator(typeDef, ctx, global)
    val symbol = Symbol.FieldTypeSymbol(typeDef.name, ctx.path, tpe)

    ctx.append(symbol).left.foreach(global.repo.error.append)
    typeDef.setSymbol(symbol)
  }

  def namedModule(module: ModuleDef)(implicit ctx: Context.RootContext, global: GlobalData): ModuleDef = {
    def tryAppendBuiltIn(symbol: Symbol.ModuleSymbol): Unit = {
      if(ctx.path.pkgName == Vector("std", "types") && global.builtin.types.names.contains(module.name))
        global.builtin.types.append(symbol)
    }

    val moduleTpe = Type.ModuleTypeGenerator(module, ctx, global)
    val moduleSymbol = Symbol.ModuleSymbol(
      module.name,
      ctx.path,
      Accessibility.Public,
      Modifier.NoModifier,
      moduleTpe
    )

    val signatureCtx = Context(ctx, moduleSymbol)
    val hps = module.hp.map(namedHPDef(_)(signatureCtx, global))
    val tps = module.tp.map(namedTypeParamDef(_)(signatureCtx, global))
    moduleSymbol.setHPs(hps.map(_.symbol.asHardwareParamSymbol))
    moduleSymbol.setTPs(tps.map(_.symbol.asTypeParamSymbol))

    tryAppendBuiltIn(moduleSymbol)
    ctx.append(moduleSymbol).left.foreach(global.repo.error.append)
    module.setSymbol(moduleSymbol)
  }

  def namedStruct(struct: StructDef)(implicit ctx: Context.RootContext, global: GlobalData): StructDef = {
    def tryAppendBuiltIn(symbol: Symbol.StructSymbol): Unit = {
      if(ctx.path.pkgName == Vector("std", "types") && global.builtin.types.names.contains(struct.name))
        global.builtin.types.append(symbol)
    }

    val structTpe = Type.StructTypeGenerator(struct, ctx, global)
    val structSymbol = Symbol.StructSymbol(
      struct.name,
      ctx.path,
      Accessibility.Public,
      Modifier.NoModifier,
      structTpe
    )

    val signatureCtx = Context(ctx, structSymbol)
    val hps = struct.hp.map(namedHPDef(_)(signatureCtx, global))
    val tps = struct.tp.map(namedTypeParamDef(_)(signatureCtx, global))
    structSymbol.setHPs(hps.map(_.symbol.asHardwareParamSymbol))
    structSymbol.setTPs(tps.map(_.symbol.asTypeParamSymbol))

    tryAppendBuiltIn(structSymbol)
    ctx.append(structSymbol).left.foreach(global.repo.error.append)
    struct.setSymbol(structSymbol)
  }

  def namedInterface(interface: InterfaceDef)(implicit ctx: Context.RootContext, global: GlobalData): InterfaceDef = {
    def tryAppendBuiltIn(symbol: Symbol.InterfaceSymbol): Unit = {
      lazy val isTraitPkg = ctx.path.pkgName == Vector("std", "traits")
      lazy val isInterfacePkg = ctx.path.pkgName == Vector("std", "interfaces")
      lazy val isBuiltInName = global.builtin.interfaces.names.contains(interface.name)

      if((isTraitPkg || isInterfacePkg) && isBuiltInName)
        global.builtin.interfaces.append(symbol)
    }

    val interfaceTpe = Type.InterfaceTypeGenerator(interface, ctx, global)
    val interfaceSymbol = Symbol.InterfaceSymbol(
      interface.name,
      ctx.path,
      Accessibility.Public,
      interface.flag,
      interfaceTpe
    )

    val signatureCtx = Context(ctx, interfaceSymbol)
    val hps = interface.hp.view.map(namedHPDef(_)(signatureCtx, global)).map(_.symbol.asHardwareParamSymbol).toVector
    val tps = interface.tp.view.map(namedTypeParamDef(_)(signatureCtx, global)).map(_.symbol.asTypeParamSymbol).toVector
    interfaceSymbol.setHPs(hps)
    interfaceSymbol.setTPs(tps)

    tryAppendBuiltIn(interfaceSymbol)
    ctx.append(interfaceSymbol).left.foreach(global.repo.error.append)
    interface.setSymbol(interfaceSymbol)
  }

  def namedEnum(enum: EnumDef)(implicit ctx: Context.RootContext, global: GlobalData): EnumDef = {
    def tryAppendBuiltIn(symbol: Symbol.EnumSymbol): Unit = {
      if(ctx.path.pkgName == Vector("std", "types") && global.builtin.types.names.contains(enum.name))
        global.builtin.types.append(symbol)
    }

    val generator = Type.EnumTypeGenerator(enum, ctx, global)
    val symbol = Symbol.EnumSymbol(
      enum.name,
      ctx.path,
      Accessibility.Public,
      Modifier.NoModifier,
      generator
    )

    val signatureCtx = Context(ctx, symbol)
    val hps = enum.hp.map(namedHPDef(_)(signatureCtx, global))
    val tps = enum.tp.map(namedTypeParamDef(_)(signatureCtx, global))
    symbol.setHPs(hps.map(_.symbol.asHardwareParamSymbol))
    symbol.setTPs(tps.map(_.symbol.asTypeParamSymbol))

    tryAppendBuiltIn(symbol)
    ctx.append(symbol).left.foreach(global.repo.error.append)
    enum.setSymbol(symbol)
  }

  def namedImplInterface(impl: ImplementInterface)(implicit ctx: Context.RootContext, global: GlobalData): ImplementInterface = {
    val implSymbol = Symbol.ImplementSymbol(impl.id, ctx.path)
    val signatureCtx = Context(ctx, implSymbol)
    val hps = impl.hp.view.map(namedHPDef(_)(signatureCtx, global)).map(_.symbol.asHardwareParamSymbol).toVector
    val tps = impl.tp.view.map(namedTypeParamDef(_)(signatureCtx, global)).map(_.symbol.asTypeParamSymbol).toVector
    implSymbol.setHPs(hps)
    implSymbol.setTPs(tps)

    impl.setSymbol(implSymbol)
  }

  def namedImplClass(impl: ImplementClass)(implicit ctx: Context.RootContext, global: GlobalData): ImplementClass = {
    val implSymbol = Symbol.ImplementSymbol(impl.id, ctx.path)
    val signatureCtx = Context(ctx, implSymbol)
    val hps = impl.hp.view.map(namedHPDef(_)(signatureCtx, global)).map(_.symbol.asHardwareParamSymbol).toVector
    val tps = impl.tp.view.map(namedTypeParamDef(_)(signatureCtx, global)).map(_.symbol.asTypeParamSymbol).toVector
    implSymbol.setHPs(hps)
    implSymbol.setTPs(tps)

    impl.setSymbol(implSymbol)
  }

  def nodeLevelNamed[T <: Definition](ast: T)(implicit ctx: Context.NodeContext, global: GlobalData): T = {
    val namedTree = ast match {
      case always: AlwaysDef => namedAlways(always)
      case method: MethodDef => namedMethod(method)
      case enum: EnumMemberDef => namedEnumMember(enum)
      case vdef: ValDef if vdef.flag.hasFlag(Modifier.Field) => namedFieldDef(vdef)
      case vdef: ValDef => namedLocalDef(vdef)
      case stage: StageDef => namedStageDef(stage)
      case state: StateDef => namedStateDef(state)
      case typeDef: TypeDef if typeDef.flag.hasFlag(Modifier.Param) => namedTypeParamDef(typeDef)
      case typeDef: TypeDef if typeDef.flag.hasFlag(Modifier.Field) => namedFieldTypeDef(typeDef)
    }

    namedTree.asInstanceOf[T]
  }

  def topLevelNamed[T <: Definition](ast: T)(implicit ctx: Context.RootContext, global: GlobalData): T = {
    val namedAST = ast match {
      case module: ModuleDef => namedModule(module)
      case struct: StructDef=> namedStruct(struct)
      case enum: EnumDef => namedEnum(enum)
      case interface: InterfaceDef => namedInterface(interface)
      case impl: ImplementInterface => namedImplInterface(impl)
      case impl: ImplementClass => namedImplClass(impl)
      case method: MethodDef => namedMethod(method)
    }

    namedAST.asInstanceOf[T]
  }
}
