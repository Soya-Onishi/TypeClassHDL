package tchdl.typecheck

import tchdl.ast._
import tchdl.util.{Symbol, Context, Type, Modifier}

object SymbolMaker {
  def make(cu: CompilationUnit): CompilationUnit = {
    val ctx = Context(None, None, Vector())
    val defs = cu.topDefs.map(makeSymbol(_, ctx))

    CompilationUnit(cu.filename, defs)
  }

  def makeSymbol(ast: Definition, ctx: Context): Definition = {
    val tpe = Type.TypeGenerator(ctx, ast)

    val symbol = ast match {
      case ModuleDef(name, _, _, _, _, _) => Symbol.TypeSymbol(name, ctx.namespace, tpe)
      case StructDef(name, _, _, _, _) => Symbol.TypeSymbol(name, ctx.namespace, tpe)
      case TypeDef(name) => Symbol.TypeSymbol(name, ctx.namespace, tpe, ctx.owner)
      case MethodDef(name, _, _, _, _, _, _) => Symbol.TermSymbol(name, ctx.namespace, tpe, ctx.owner).setFlag(Modifier.Method)
      case ValDef(mod, name, _, _) => Symbol.TermSymbol(name, ctx.namespace, tpe, ctx.owner).setFlag(mod)
      case AlwaysDef(name, _) => Symbol.TermSymbol(name, ctx.namespace, tpe, ctx.owner).setFlag(Modifier.Always)
      case StageDef(name, _, _, _, _) => Symbol.TermSymbol(name, ctx.namespace, tpe, ctx.owner).setFlag(Modifier.Stage)
      case StateDef(name, _) => Symbol.TermSymbol(name, ctx.namespace, tpe, ctx.owner).setFlag(Modifier.State)
    }

    ast.setSymbol(symbol)
  }
}
