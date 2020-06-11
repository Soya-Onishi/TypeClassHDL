package tchdl.typecheck

import tchdl.ast._
import tchdl.util.{Error, Reporter, Symbol, Context}
import tchdl.util.TchdlException.ImplementationErrorException

object NamerPost {
  def exec(cu: CompilationUnit): Unit = {
    verifyImport(cu)
    importPreludes(cu)
  }

  private def getContext(cu: CompilationUnit): Context.RootContext =
    Symbol.RootPackageSymbol.search(cu.pkgName)
      .getOrElse(throw new ImplementationErrorException(s"package ${cu.pkgName.mkString("::")} is not found"))
      .lookupCtx(cu.filename.get)
      .getOrElse(throw new ImplementationErrorException(s"context for ${cu.filename.get} is not found"))

  private def verifyImport(cu: CompilationUnit): Unit = {
    val ctx = getContext(cu)

    val verifiedImports = cu.imports.map { imprt =>
      Symbol.RootPackageSymbol
        .search(imprt.dropRight(1))
        .left.map(Error.SymbolNotFound.apply)
        .flatMap { packageSymbol =>
          val name = imprt.last
          packageSymbol.lookup[Symbol.TypeSymbol](name).toEither
        }
    }

    val (errs, symbols) = verifiedImports.partitionMap(identity)

    if(errs.nonEmpty) Reporter.appendError(Error.MultipleErrors(errs: _*))
    else symbols.foreach(ctx.appendImportSymbol(_).left.foreach(Reporter.appendError))
  }

  private def importPreludes(cu: CompilationUnit): Unit = {
    val preludes = Symbol.builtInSymbols
    val ctx = getContext(cu)
    val (errs, _) = preludes.map(ctx.appendPrelude(_)).partitionMap(identity)
    errs.foreach(Reporter.appendError)
  }
}
