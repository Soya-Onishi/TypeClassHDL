package tchdl.typecheck

import tchdl.ast._
import tchdl.util.TchdlException.ImplimentationErrorException
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
        val moduleSym: Symbol = ???

        module.setSymbol(moduleSym)
      case struct: StructDef=>
        val structSym: Symbol = ???

        struct.setSymbol(structSym)
      case always: AlwaysDef =>
        val alwaysSym: Symbol = ???

        always.setSymbol(alwaysSym)
      case method: MethodDef =>
        val methodSym: Symbol = ???

        method.setSymbol(methodSym)
      case vdef: ValDef =>
        val valSym: Symbol = ???

        vdef.setSymbol(valSym)
      case stage: StageDef =>
        val stageSym: Symbol = ???

        stage.setSymbol(stageSym)
      case state: StateDef =>
        val stateSym: Symbol = ???

        state.setSymbol(stateSym)
      case typeDef: TypeDef =>
        val typeSym: Symbol = ???

        typeDef.setSymbol(typeSym)
      case _ =>
        val msg = s"Namer is not implemented for [${ast.getClass.getName}]"
        throw new ImplimentationErrorException(msg)
    }

    namedAST.asInstanceOf[T]
  }
}
