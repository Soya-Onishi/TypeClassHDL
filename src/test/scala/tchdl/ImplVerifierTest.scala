package tchdl

import tchdl.ast._
import tchdl.typecheck._
import tchdl.util._

import org.scalatest.funsuite.AnyFunSuite

class ImplVerifierTest extends AnyFunSuite {
  private def parse(filename: String) = parseFile(_.compilation_unit)((gen, tree) => gen(tree, filename))(filename)
  private def untilImplVerify(filenames: String*)(implicit global: GlobalData): Seq[CompilationUnit] = {
    val trees = filenames.map(parse).map(_.asInstanceOf[CompilationUnit])

    trees.foreach(Namer.exec)
    if(global.repo.error.counts > 0) fail(global.repo.error.elems.mkString("\n"))

    trees.foreach(NamerPost.exec)
    if(global.repo.error.counts > 0) fail(global.repo.error.elems.mkString("\n"))

    trees.foreach(ImplVerifier.exec)
    ImplVerifier.verifyImplConflict()

    trees
  }

  def showErrors(errors: Vector[Error]): String =
    errors.map(_.debugString).mkString("\n\n")

  test("verify most simple conflict") {
    implicit val global: GlobalData = new GlobalData
    val impl0 = Vector(rootDir, filePath, "impl0.tchdl").mkString("/")
    val filenames = impl0 +: builtInFiles
    val trees = untilImplVerify(filenames: _*)

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
    implicit val global: GlobalData = new GlobalData
    val filename = Vector(rootDir, filePath, "impl1.tchdl").mkString("/")
    val filenames = filename +: builtInFiles
    val trees = untilImplVerify(filenames: _*)

    if(global.repo.error.counts > 0) fail(showErrors(global.repo.error.elems))
  }

  test("verify actually overlap hardware parameter") {
    implicit val global: GlobalData = new GlobalData
    val filename = Vector(rootDir, filePath, "impl2.tchdl").mkString("/")
    val filenames = filename +: builtInFiles
    val trees = untilImplVerify(filenames: _*)

    assert(global.repo.error.counts == 1, showErrors(global.repo.error.elems))
    val err = global.repo.error.elems.head
    assert(err.isInstanceOf[Error.ImplementInterfaceConflict], showErrors(global.repo.error.elems))
  }

  test("verify no conflict type parameter") {
    implicit val global: GlobalData = new GlobalData
    val filename = Vector(rootDir, filePath, "impl3.tchdl").mkString("/")
    val filenames = filename +: builtInFiles
    val trees = untilImplVerify(filenames: _*)

    assert(global.repo.error.counts == 0, showErrors(global.repo.error.elems))
    val tree = trees.find(_.filename.get == filename).get
    val interface = tree.topDefs.find(_.symbol.isInterfaceSymbol).get
    val impls = interface.symbol.asInterfaceSymbol.impls

    assert(impls.length == 2)
  }

  test("verify no conflict between a poly type and a mono type in type parameter") {
    implicit val global: GlobalData = new GlobalData
    val filename = Vector(rootDir, filePath, "impl4.tchdl").mkString("/")
    val filenames = filename +: builtInFiles
    val trees = untilImplVerify(filenames: _*)

    assert(global.repo.error.counts == 0, showErrors(global.repo.error.elems))
  }

  test("verify actually conflict between a poly type and a mono type in type parameter") {
    implicit val global: GlobalData = new GlobalData
    val filename = buildName(rootDir, filePath, "impl5.tchdl")
    val filenames = filename +: builtInFiles
    val trees = untilImplVerify(filenames: _*)

    assert(global.repo.error.counts == 1, showErrors(global.repo.error.elems))
    val err = global.repo.error.elems.head
    assert(err.isInstanceOf[Error.ImplementInterfaceConflict])
  }

  test("verify no conflict because of using same type parameter") {
    implicit val global: GlobalData = new GlobalData
    val filename = buildName(rootDir, filePath, "impl6.tchdl")
    val filenames = filename +: builtInFiles
    val trees = untilImplVerify(filenames: _*)

    assert(global.repo.error.counts == 0, showErrors(global.repo.error.elems))
  }

  test("verify complicated conflict0") {
    val global = new GlobalData
    val filename = buildName(rootDir, filePath, "impl7.tchdl")
    val filenames = filename +: builtInFiles
    val trees = untilImplVerify(filenames: _*)(global)

    assert(global.repo.error.counts == 0, showErrors(global.repo.error.elems))
  }

  test("complicated conflict verification. This does not cause error") {
    val global = new GlobalData
    val filename = buildName(rootDir, filePath, "impl8.tchdl")
    val filenames = filename +: builtInFiles
    val trees = untilImplVerify(filenames: _*)(global)

    assert(global.repo.error.counts == 0, showErrors(global.repo.error.elems))
  }

  test("complicated conflict verification. This cause error because of implementation of I0 for ST[T]") {
    val global = new GlobalData
    val filename = buildName(rootDir, filePath, "impl9.tchdl")
    val filenames = filename +: builtInFiles
    val trees = untilImplVerify(filenames: _*)(global)

    assert(global.repo.error.counts == 1, showErrors(global.repo.error.elems))
  }

}
