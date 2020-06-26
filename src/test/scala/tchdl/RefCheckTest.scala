package tchdl

import tchdl.typecheck._
import tchdl.util._
import tchdl.ast._

class RefCheckTest extends TchdlFunSuite {
  def parse(filename: String): CompilationUnit =
    parseFile(_.compilation_unit)((gen, tree) => gen(tree, filename))(filename).asInstanceOf[CompilationUnit]

  def untilThisPhase(names: String*): (Seq[CompilationUnit], GlobalData) = {
    implicit val global: GlobalData = GlobalData()
    val files = names.map(buildName(rootDir, filePath, _))
    val filenames = files ++ builtInFiles
    val trees = filenames.map(parse)

    trees.foreach(Namer.exec)
    expectNoError(global)

    trees.foreach(NamerPost.exec)
    expectNoError(global)

    trees.foreach(BuildImplContainer.exec)
    expectNoError(global)

    VerifyImplConflict.verifyImplConflict()
    expectNoError

    val trees0 = trees.map(TopDefTyper.exec)
    expectNoError

    trees0.foreach(ImplMethodSigTyper.exec)
    expectNoError

    val trees1 = trees0.map(Typer.exec)
    expectNoError

    trees1.foreach(RefCheck.exec)

    val cus = trees1.filter(cu => files.contains(cu.filename.get))
    (cus, global)
  }

  test("reference check causes no error in ALU") {
    val (_, global) = untilThisPhase("ALU.tchdl")
    expectNoError(global)
  }

  test("refer sibling method from parent module") {
    val (_, global) = untilThisPhase("referSubmodSibling.tchdl")
    expectError(1)(global)

    val err = global.repo.error.elems.head
    assert(err.isInstanceOf[Error.CallInvalid])
  }

  test("refer parent method from parent module") {
    val (_, global) = untilThisPhase("referSubmodParent.tchdl")
    expectError(1)(global)

    val err = global.repo.error.elems.head
    assert(err.isInstanceOf[Error.CallInvalid])
  }

  test("refer input method from sibling module") {
    val (_, global) = untilThisPhase("referSiblingInput.tchdl")
    expectError(1)(global)

    val err = global.repo.error.elems.head
    assert(err.isInstanceOf[Error.CallInvalid])
  }

  test("refer input method of parent module") {
    val (_, global) =untilThisPhase("referParentInput.tchdl")
    expectError(1)(global)

    val err = global.repo.error.elems.head
    assert(err.isInstanceOf[Error.CallInvalid])
  }
}
