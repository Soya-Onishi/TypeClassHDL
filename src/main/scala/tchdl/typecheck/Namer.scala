package tchdl.typecheck

import tchdl.ast._
import tchdl.util.{Symbol, TchdlException}

class Namer {
  def exec(cu: CompilationUnit): Unit = {
    named(cu)
  }

  private def named[T](ast: T): T = {
    val namedAST = ast match {
      case cu @ CompilationUnit(_, topDefs) =>
        val namedDefs = topDefs.map(named)
        CompilationUnit(cu.filename, namedDefs)
      case module: ModuleDef =>
        val namedHp = module.hp.map(named)
        val namedTp = module.tp.map(named)
        ??? // val namedPassedModule = ???
        val namedComponents = module.components.map(named)

        val moduleSym: Symbol = ???

        ModuleDef(
          module.name,
          namedHp,
          namedTp,
          module.bounds,
          ???,
          namedComponents
        ).setSymbol(moduleSym)
      case s @ StructDef(_, hp, tp, bounds, fields) =>
        val namedHp = hp.map(named)
        val namedTp = tp.map(named)
        val namedFields = fields.map(named)

        val structSym: Symbol = ???

        StructDef(
          s.name,
          namedHp,
          namedTp,
          bounds,
          namedFields
        ).setSymbol(structSym)
      case always @ AlwaysDef(_, blk) =>
        val namedBlk = named(blk)

        val alwaysSym: Symbol = ???

        AlwaysDef(always.name, namedBlk).setSymbol(alwaysSym)
      case method @ MethodDef(_, hp, tp, _, params, _, blk) =>
        val namedHp = hp.map(named)
        val namedTp = tp.map(named)
        val namedParams = params.map(named)
        val namedBlk = named(blk)

        val methodSym: Symbol = ???

        MethodDef(
          method.name,
          namedHp,
          namedTp,
          method.bounds,
          namedParams,
          method.retTpe,
          namedBlk
        ).setSymbol(methodSym)
      case vdef: ValDef =>
        val namedExpr = vdef.expr.map(named)

        val valSym: Symbol = ???

        ValDef(vdef.flag, vdef.name, vdef.tpeTree, namedExpr).setSymbol(valSym)
      case stage: StageDef =>
        val namedParams = stage.params.map(named)
        val namedStates = stage.states.map(named)
        val namedBlk = stage.blk.map(named)

        val stageSym: Symbol = ???

        StageDef(
          stage.name,
          namedParams,
          stage.retTpe,
          namedStates,
          namedBlk
        ).setSymbol(stageSym)
      case state: StateDef =>
        val namedBlk = named(state.blk)

        val stateSym: Symbol = ???

        StateDef(state.name, namedBlk).setSymbol(stateSym)
      case typeDef: TypeDef =>
        val typeSym: Symbol = ???

        TypeDef(typeDef.name).setSymbol(typeSym)
      case blk: Block =>
        val namedElems = blk.elems.map(named)

        Block(namedElems, blk.last)
      case _ => ast
    }

    namedAST.asInstanceOf[T]
  }
}
