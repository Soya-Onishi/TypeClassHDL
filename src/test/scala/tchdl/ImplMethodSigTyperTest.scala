package tchdl

import tchdl.ast._
import tchdl.util._
import tchdl.typecheck._

class ImplMethodSigTyperTest extends TchdlFunSuite {
  def parse(filename: String): CompilationUnit =
    parseFile(_.compilation_unit)((gen, tree) => gen(tree, filename))(filename).asInstanceOf[CompilationUnit]

  def untilThisPhase(names: String*): (Seq[CompilationUnit], GlobalData) = {
    implicit val global: GlobalData = new GlobalData

    val files = names.map(buildName(rootDir, filePath, _))
    val filenames = files ++ builtInFiles
    val trees = filenames.map(parse)

    trees.foreach(Namer.exec)
    expectNoError

    trees.foreach(NamerPost.exec)
    expectNoError

    trees.foreach(BuildImplContainer.exec)
    expectNoError

    VerifyImplConflict.verifyImplConflict()
    expectNoError

    trees.foreach(TopDefTyper.exec)
    expectNoError

    trees.foreach(ImplMethodSigTyper.exec)

    val cus = trees.filter(cu => files.contains(cu.filename.get))
    (cus, global)
  }

  test("reject invalid signature impl's method") {
    val (_, global) = untilThisPhase("typerDefSig0.tchdl")
    expectError(1)(global)

    val err = global.repo.error.elems.head
    assert(err.isInstanceOf[Error.TypeMissMatch])
    val Error.TypeMissMatch(expect, actual) = err
    assert(expect == Type.intTpe(global))
    assert(actual == Type.stringTpe(global))
  }

  test("reject poly method that does not have same bounds as original") {
    val (_, global) = untilThisPhase("typerDefSig1.tchdl")
    expectError(1)(global)

    val err = global.repo.error.elems.head
    assert(err.isInstanceOf[Error.NotEnoughTPBound], showErrors(global))
  }
}
