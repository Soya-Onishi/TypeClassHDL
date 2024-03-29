package tchdl.typecheck

import tchdl.ast._
import tchdl.util._
import tchdl.util.TchdlException.ImplementationErrorException

object NamerPost {
  def exec(cu: CompilationUnit)(implicit global: GlobalData): CompilationUnit = {
    verifyImport(cu)
    importPreludes(cu)

    cu
  }

  private def getContext(cu: CompilationUnit)(implicit global: GlobalData): Context.RootContext =
    global.rootPackage.search(cu.pkgName)
      .getOrElse(throw new ImplementationErrorException(s"package ${cu.pkgName.mkString("::")} is not found"))
      .lookupCtx(cu.filename)
      .getOrElse(throw new ImplementationErrorException(s"context for ${cu.filename} is not found"))

  private def verifyImport(cu: CompilationUnit)(implicit global: GlobalData): Unit = {
    val ctx = getContext(cu)

    val verifiedImports = cu.imports.map { imprt =>
      global.rootPackage
        .search(imprt.dropRight(1))
        .flatMap { packageSymbol =>
          val name = imprt.last
          packageSymbol.lookup[Symbol.TypeSymbol](name).toEither
        }
    }

    val (errs, symbols) = verifiedImports.partitionMap(identity)

    if(errs.nonEmpty) global.repo.error.append(Error.MultipleErrors(errs: _*))
    else symbols.foreach(ctx.appendImportSymbol(_).left.foreach(global.repo.error.append))
  }

  private def importPreludes(cu: CompilationUnit)(implicit global: GlobalData): Unit = {
    val preludes = global.builtin.types.symbols
    val ctx = getContext(cu)
    val (errs, _) = preludes.map(ctx.appendPrelude(_)).partitionMap(identity)

    errs.foreach(global.repo.error.append)
  }
}
