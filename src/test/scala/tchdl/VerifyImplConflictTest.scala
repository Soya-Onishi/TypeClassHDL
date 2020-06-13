package tchdl

import tchdl.ast._
import tchdl.typecheck._
import tchdl.util._

import org.scalatest.funsuite.AnyFunSuite

class VerifyImplConflictTest extends AnyFunSuite {
  private def parse(filename: String) = parseFile(_.compilation_unit)((gen, tree) => gen(tree, filename))(filename)
  private def untilImplVerify(names: String*): (Seq[CompilationUnit], GlobalData) = {
    implicit val global: GlobalData = new GlobalData
    val filename = names.map(buildName(rootDir, filePath, _))
    val filenames = filename ++ builtInFiles
    val trees = filenames.map(parse).map(_.asInstanceOf[CompilationUnit])

    trees.foreach(Namer.exec)
    assert(global.repo.error.counts == 0, global.repo.error.elems.mkString("\n"))

    trees.foreach(NamerPost.exec)
    assert(global.repo.error.counts == 0, global.repo.error.elems.mkString("\n"))

    trees.foreach(BuildImplContainer.exec)
    assert(global.repo.error.counts == 0, global.repo.error.elems.mkString("\n"))

    VerifyImplConflict.verifyImplConflict()

    (trees, global)
  }

  test("verify most simple conflict") {
    val (trees, global) = untilImplVerify("impl0.tchdl")
    VerifyImplConflict.verifyImplConflict()(global)

    if(global.repo.error.counts > 0) fail(global.repo.error.elems.mkString("\n"))
    val cu = trees.head

    val interface = cu.topDefs.collectFirst{ case interface: InterfaceDef => interface }.get
    assert(interface.symbol.isInstanceOf[Symbol.InterfaceSymbol])

    val impls = interface.symbol.asInterfaceSymbol.impls
    assert(impls.length == 2)

    val implForST0 = impls.find(_.targetType.origin.name == "ST0")
    val implForST1 = impls.find(_.targetType.origin.name == "ST1")
    assert(implForST0.isDefined)
    assert(implForST1.isDefined)
  }

  test("verify no conflict hardware parameter") {
    val (trees, global) = untilImplVerify("impl1.tchdl")
    VerifyImplConflict.verifyImplConflict()(global)

    if(global.repo.error.counts > 0) fail(showErrors(global.repo.error.elems))
  }

  test("verify actually overlap hardware parameter") {
    val (trees, global) = untilImplVerify("impl2.tchdl")
    VerifyImplConflict.verifyImplConflict()(global)

    assert(global.repo.error.counts == 1, showErrors(global.repo.error.elems))
    val err = global.repo.error.elems.head
    assert(err.isInstanceOf[Error.ImplementInterfaceConflict], showErrors(global.repo.error.elems))
  }

  test("verify no conflict type parameter") {
    val (trees, global) = untilImplVerify("impl3.tchdl")
    VerifyImplConflict.verifyImplConflict()(global)

    assert(global.repo.error.counts == 0, showErrors(global.repo.error.elems))
    val tree = trees.find(_.filename.get == buildName(rootDir, filePath, "impl3.tchdl")).get
    val interface = tree.topDefs.find(_.symbol.isInterfaceSymbol).get
    val impls = interface.symbol.asInterfaceSymbol.impls

    assert(impls.length == 2)
  }

  test("verify no conflict between a poly type and a mono type in type parameter") {
    val (trees, global) = untilImplVerify("impl4.tchdl")
    VerifyImplConflict.verifyImplConflict()(global)

    assert(global.repo.error.counts == 0, showErrors(global.repo.error.elems))
  }

  test("verify actually conflict between a poly type and a mono type in type parameter") {
    val (_, global) = untilImplVerify("impl5.tchdl")
    VerifyImplConflict.verifyImplConflict()(global)

    assert(global.repo.error.counts == 1, showErrors(global.repo.error.elems))
    val err = global.repo.error.elems.head
    assert(err.isInstanceOf[Error.ImplementInterfaceConflict])
  }

  test("verify no conflict because of using same type parameter") {
    val (_, global) = untilImplVerify("impl6.tchdl")
    VerifyImplConflict.verifyImplConflict()(global)

    assert(global.repo.error.counts == 0, showErrors(global.repo.error.elems))
  }

  test("verify complicated conflict0") {
    val (_, global) = untilImplVerify("impl7.tchdl")
    VerifyImplConflict.verifyImplConflict()(global)

    assert(global.repo.error.counts == 0, showErrors(global.repo.error.elems))
  }

  test("complicated conflict verification. This does not cause error") {
    val (_, global) = untilImplVerify("impl8.tchdl")
    VerifyImplConflict.verifyImplConflict()(global)

    assert(global.repo.error.counts == 0, showErrors(global.repo.error.elems))
  }

  test("complicated conflict verification. This cause error because of implementation of I0 for ST[T]") {
    val (_, global) = untilImplVerify("impl9.tchdl")
    VerifyImplConflict.verifyImplConflict()(global)

    assert(global.repo.error.counts == 1, showErrors(global.repo.error.elems))
    val err = global.repo.error.elems.head
    assert(err.isInstanceOf[Error.ImplementInterfaceConflict], showErrors(global.repo.error.elems))
  }

  test("impl for type parameter as target. this does not cause error") {
    val (_, global) = untilImplVerify("impl10.tchdl")
    VerifyImplConflict.verifyImplConflict()(global)

    assert(global.repo.error.counts == 0, showErrors(global.repo.error.elems))
  }

  test("impl for type parameter as target. this causes implement conflict error") {
    val (trees, global) = untilImplVerify("impl11.tchdl")
    VerifyImplConflict.verifyImplConflict()(global)

    assert(global.repo.error.counts == 1, showErrors(global.repo.error.elems))
    val err = global.repo.error.elems.head
    assert(err.isInstanceOf[Error.ImplementInterfaceConflict], showErrors(global.repo.error.elems))
  }
}
