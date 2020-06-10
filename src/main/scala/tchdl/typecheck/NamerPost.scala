package tchdl.typecheck

import tchdl.ast._
import tchdl.util.{Error, LookupResult, Reporter, Symbol}
import tchdl.util.TchdlException.ImplementationErrorException

object NamerPost {
  def verifyImport(cu: CompilationUnit): Unit = {
    val ctx = Symbol.RootPackageSymbol.search(cu.pkgName)
      .getOrElse(throw new ImplementationErrorException(s"package ${cu.pkgName.mkString("::")} is not found"))
      .lookupCtx(cu.filename.get)
      .getOrElse(throw new ImplementationErrorException(s"context for ${cu.filename.get} is not found"))

    val verifiedImports = cu.imports.map { imprt =>
      Symbol.RootPackageSymbol
        .search(imprt.dropRight(1))
        .left.map(Error.SymbolNotFound.apply)
        .flatMap { packageSymbol =>
          val name = imprt.last
          packageSymbol.lookup(name).toEither
        }
    }

    verifiedImports.foreach {
      case Right(symbol) => ctx.appendImportSymbol(symbol).left.foreach(Reporter.appendError)
      case Left(err) => Reporter.appendError(err)
    }
  }
}