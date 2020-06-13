package tchdl

import tchdl.typecheck._
import tchdl.util._
import tchdl.ast._

import org.scalatest.funsuite.AnyFunSuite

class TyperTest extends AnyFunSuite {
  def parse(filename: String): CompilationUnit =
    parseFile(_.compilation_unit)((gen, tree) => gen(tree, filename))(filename).asInstanceOf[CompilationUnit]

  def untilTyper(names: String*): (Vector[CompilationUnit], GlobalData) = {
    implicit val global: GlobalData = new GlobalData
    val specifiedFileNames = names.map(buildName(rootDir, filePath, _))
    val filenames = specifiedFileNames ++ builtInFiles
    val trees = filenames.map(parse)

    trees.foreach(Namer.exec)
    assert(global.repo.error.counts == 0, showErrors(global.repo.error.elems))

    trees.foreach(NamerPost.exec)
    assert(global.repo.error.counts == 0, showErrors(global.repo.error.elems))

    trees.foreach(ImplVerifier.exec)
    assert(global.repo.error.counts == 0, showErrors(global.repo.error.elems))

    ImplVerifier.verifyImplConflict()
    assert(global.repo.error.counts == 0, showErrors(global.repo.error.elems))

    val typedTrees = trees.map(Typer.exec)
    val returnedTrees = typedTrees
      .filter(tt => specifiedFileNames.contains(tt.filename.get))
      .toVector

    (returnedTrees, global)
  }

  test("lookup ST's field. This does not cause errors") {
    val (trees, global) = untilTyper("structImpl0.tchdl")
    assert(global.repo.error.counts == 0, showErrors(global.repo.error.elems))
  }

  test("lookup ST's impl method. This does not cause errors") {
    val (trees, global) = untilTyper("structImpl1.tchdl")
    assert(global.repo.error.counts == 0, showErrors(global.repo.error.elems))

    val topDefs = trees.head.topDefs
    val Vector(methodF, methodG) = topDefs
      .collect{ case impl: ImplementClass => impl }
      .head
      .methods

    val Apply(select: Select, _, _, _) = methodF.blk.get.last
    assert(select.symbol == methodG.symbol)
  }
}
