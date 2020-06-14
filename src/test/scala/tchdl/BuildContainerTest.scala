package tchdl

import tchdl.ast._
import tchdl.util._
import tchdl.typecheck._

class BuildContainerTest extends TchdlFunSuite {
  def parse(filename: String): CompilationUnit =
    parseFile(_.compilation_unit)((gen, tree) => gen(tree, filename))(filename).asInstanceOf[CompilationUnit]

  def untilBuild(names: String*): (Seq[CompilationUnit], GlobalData) = {
    implicit val global: GlobalData = new GlobalData
    val filename = names.map(buildName(rootDir, filePath, _))
    val filenames = filename ++ builtInFiles
    val trees = filenames.map(parse)

    trees.foreach(Namer.exec)
    assert(global.repo.error.counts == 0, global.repo.error.elems.mkString("\n"))

    trees.foreach(NamerPost.exec)
    assert(global.repo.error.counts == 0, global.repo.error.elems.mkString("\n"))

    trees.foreach(BuildImplContainer.exec)

    (trees, global)
  }

  test("struct bounds miss match type between Num and Str") {
    val (_, global) = untilBuild("typeCheckHP0.tchdl")

    assert(global.repo.error.counts == 1, showErrors(global))
    val err = global.repo.error.elems.head
    assert(err.isInstanceOf[Error.TypeMissMatch], showErrors(global))
  }

  test("interface impl's hardware parameter miss match type between Num and Str") {
    val (_, global) = untilBuild("typeCheckHP1.tchdl")

    assert(global.repo.error.counts == 1, showErrors(global))
    val err = global.repo.error.elems.head
    assert(err.isInstanceOf[Error.TypeMissMatch], showErrors(global))
  }
}
