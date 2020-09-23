package tchdl

import tchdl.ast._
import tchdl.typecheck._
import tchdl.util._

class ProcVerifierTest extends TchdlFunSuite {
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
    trees1.foreach(ProcVerifier.exec)

    val cus = trees1.filter(cu => files.contains(cu.filename))
    (cus, global)
  }

  test("run normal procedure definition") {
    val (_, global) = untilThisPhase("procNoError.tchdl")
    expectNoError(global)
  }

  test("proc block does not have exhaustive flow control") {
    val (_, global) = untilThisPhase("procNoExhaustive.tchdl")
    expectError(1)(global)

    val err = global.repo.error.elems.head
    assert(err.isInstanceOf[Error.ControlFlowNotExhaustive])
  }

  test("use if expression to select next block exhaustively not cause error") {
    val (_, global) = untilThisPhase("procIfControl.tchdl")
    expectNoError(global)
  }
}
