package tchdl

import tchdl.ast._
import tchdl.util._
import tchdl.typecheck._

import org.scalatest.funsuite.AnyFunSuite

class TopDefTyperTest extends AnyFunSuite {
  def parse(filename: String): CompilationUnit =
    parseFile(_.compilation_unit)((gen, tree) => gen(tree, filename))(filename).asInstanceOf[CompilationUnit]

  def untilTopDefTyper(names: String*): (Seq[CompilationUnit], GlobalData) = {
    implicit val global: GlobalData = new GlobalData
    val files = names.map(buildName(rootDir, filePath, _))
    val filenames = files ++ builtInFiles

    val trees0 = filenames.map(parse)

    trees0.foreach(Namer.exec)
    expectNoError

    trees0.foreach(NamerPost.exec)
    expectNoError

    trees0.foreach(BuildImplContainer.exec)
    expectNoError

    VerifyImplConflict.verifyImplConflict()
    expectNoError

    val trees1 = trees0.map(TopDefTyper.exec)

    (trees1, global)
  }

  test("not meet bounds for type parameter in impl's interface") {
    val (_, global) = untilTopDefTyper("topdef0.tchdl")
    expectError(1)(global)

    val error = global.repo.error.elems.head
    assert(error.isInstanceOf[Error.NotMeetPartialTPBound])
  }

  test("not meet bounds for type parameter in impl's target type") {
    val (_, global) = untilTopDefTyper("topdef0.tchdl")
    expectError(1)(global)

    val error = global.repo.error.elems.head
    assert(error.isInstanceOf[Error.NotMeetPartialTPBound])
  }

}
