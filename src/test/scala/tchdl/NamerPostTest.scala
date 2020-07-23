package tchdl

import tchdl.ast._
import tchdl.util._
import tchdl.typecheck._

class NamerPostTest extends TchdlFunSuite {
  private def parse(file: String): CompilationUnit =
    parseFile(_.compilation_unit)((gen, tree) => gen(tree, file))(file).asInstanceOf[CompilationUnit]

  test("verify imports") {
    implicit val global: GlobalData = GlobalData()

    val imports = Vector("import0", "import1")
    val files = imports.map(imp => Vector(rootDir, filePath, imp + ".tchdl").mkString("/")) ++ builtInFiles
    val trees = files.map(parse)
    trees.foreach(Namer.exec)
    trees.foreach(NamerPost.exec)

    assert(global.repo.error.counts == 0, global.repo.error.elems.map(_.toString).mkString("\n"))

    (imports zip files).foreach { case (imp, file) =>
      val importPath = Vector("test", imp)
      val pkg = global.rootPackage
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

  test("verify all builtin types imported in collect") {
    implicit val global: GlobalData = GlobalData()
    val builtin = Vector(rootDir, builtinPath, "types.tchdl").mkString("/")
    val filename = Vector(rootDir, filePath, "prelude.tchdl").mkString("/")
    val trees = Vector(filename, builtin).map(parse)
    trees.foreach(Namer.exec)
    trees.foreach(NamerPost.exec)

    val Right(pkg) = global.rootPackage.search(Vector("prelude"))
    val ctx = pkg.lookupCtx(filename).get

    val builtinNames = Vector(
      "Int",
      "Bit",
      "Unit",
      "String",
      "Num",
      "Str"
    )

    val results = builtinNames.map(ctx.lookup[Symbol.TypeSymbol](_))
    results.foreach {
      case LookupResult.LookupSuccess(_) =>
      case LookupResult.LookupFailure(err) => fail(err.toString)
    }
  }

  test("importing From trait works correctly") {
    implicit val global: GlobalData = GlobalData()

    val filename = Vector(rootDir, filePath, "useFroms.tchdl").mkString("/")
    val filenames = filename +: builtInFiles
    val trees = filenames.map(parse)
    trees.foreach(Namer.exec)
    expectNoError

    trees.foreach(NamerPost.exec)
    expectNoError

    val ctx = global.rootPackage.search(Vector("test")).getOrElse(fail()).lookupCtx(filename).get
    val traits = ctx.interfaceTable

    assert(traits.values.toVector.length == 1)
    assert(traits.keys.head == "From")
  }
}
