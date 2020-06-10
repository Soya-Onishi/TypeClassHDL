package tchdl

import tchdl.ast._
import tchdl.util._
import tchdl.typecheck._

import org.scalatest.funsuite.AnyFunSuite

class NamerPostTest extends AnyFunSuite {
  private def parse(file: String): CompilationUnit =
    parseFile(_.compilation_unit)((gen, tree) => gen(tree, file))(file).asInstanceOf[CompilationUnit]

  test("verify imports") {
    val imports = Vector("import0", "import1")
    val files = imports.map(imp => Vector(rootDir, filePath, imp + ".tchdl").mkString("/"))
    val trees = files.map(parse)
    trees.foreach(Namer.exec)
    trees.foreach(NamerPost.verifyImport)

    assert(Reporter.errorCounts == 0, Reporter.errors.map(_.toString).mkString("\n"))

    (imports zip files).foreach { case (imp, file) =>
      val importPath = Vector("test", imp)
      val pkg = Symbol.RootPackageSymbol
        .search(importPath)
        .getOrElse(fail(s"${importPath.mkString("::")} does not found"))

      val ctx = pkg.lookupCtx(file).getOrElse(fail(s"context[$file] does not found"))
      Vector("Type0", "Type1").foreach {
        ctx.lookup[Symbol.EntityTypeSymbol](_) match {
          case LookupResult.LookupFailure(err) => fail(s"lookup failed [$err]")
          case LookupResult.LookupSuccess(_) =>
        }
      }
    }
  }
}
