package tchdl

import tchdl.ast._
import tchdl.typecheck._
import tchdl.util._

import org.scalatest.funsuite.AnyFunSuite

class ImplVerifierTest extends AnyFunSuite {
  private def parse(filename: String) = parseFile(_.compilation_unit)((gen, tree) => gen(tree, filename))(filename)
  private def untilImplVerify(filenames: String*): Seq[CompilationUnit] = {
    val trees = filenames.map(parse).map(_.asInstanceOf[CompilationUnit])

    trees.foreach(Namer.exec)
    if(Reporter.errorCounts > 0) fail(Reporter.errors.mkString("\n"))

    trees.foreach(NamerPost.exec)
    if(Reporter.errorCounts > 0) fail(Reporter.errors.mkString("\n"))

    trees.foreach(ImplVerifier.exec)

    trees
  }

  test("verify most simple conflict") {
    val impl0 = Vector(rootDir, filePath, "impl0.tchdl").mkString("/")
    val filenames = impl0 +: builtInFiles
    val trees = untilImplVerify(filenames: _*)

    if(Reporter.errorCounts > 0) fail(Reporter.errors.mkString("\n"))
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

  test("verify conflict hardware parameter") {
    val filename = Vector(rootDir, filePath, "impl1.tchdl").mkString("/")
    val filenames = filename +: builtInFiles
    val trees = untilImplVerify(filenames: _*)

    if(Reporter.errorCounts > 0) fail(Reporter.errors.map(_.debugString).mkString("\n\n"))
  }
}
