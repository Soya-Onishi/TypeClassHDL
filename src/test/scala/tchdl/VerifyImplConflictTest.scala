package tchdl

import tchdl.ast._
import tchdl.typecheck._
import tchdl.util._

class VerifyImplConflictTest extends TchdlFunSuite {
  private def parse(filename: String) = parseFile(_.compilation_unit)((gen, tree) => gen(tree, filename))(filename)
  private def untilImplVerify(names: String*): (Seq[CompilationUnit], GlobalData) = {
    implicit val global: GlobalData = GlobalData()
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

    if(global.repo.error.counts > 0) fail(showErrors(global))
  }

  test("verify actually overlap hardware parameter") {
    val (trees, global) = untilImplVerify("impl2.tchdl")

    assert(global.repo.error.counts == 1, showErrors(global))
    val err = global.repo.error.elems.head
    assert(err.isInstanceOf[Error.ImplementInterfaceConflict], showErrors(global))
  }

  test("verify no conflict type parameter") {
    val (trees, global) = untilImplVerify("impl3.tchdl")

    assert(global.repo.error.counts == 0, showErrors(global))
    val tree = trees.find(_.filename.get == buildName(rootDir, filePath, "impl3.tchdl")).get
    val interface = tree.topDefs.find(_.symbol.isInterfaceSymbol).get
    val impls = interface.symbol.asInterfaceSymbol.impls

    assert(impls.length == 2)
  }

  test("verify no conflict between a poly type and a mono type in type parameter") {
    val (trees, global) = untilImplVerify("impl4.tchdl")

    assert(global.repo.error.counts == 0, showErrors(global))
  }

  test("verify actually conflict between a poly type and a mono type in type parameter") {
    val (_, global) = untilImplVerify("impl5.tchdl")

    assert(global.repo.error.counts == 1, showErrors(global))
    val err = global.repo.error.elems.head
    assert(err.isInstanceOf[Error.ImplementInterfaceConflict])
  }

  test("verify no conflict because of using same type parameter") {
    val (_, global) = untilImplVerify("impl6.tchdl")

    assert(global.repo.error.counts == 0, showErrors(global))
  }

  test("verify complicated conflict0") {
    val (_, global) = untilImplVerify("impl7.tchdl")

    assert(global.repo.error.counts == 0, showErrors(global))
  }

  test("complicated conflict verification. This does not cause error") {
    val (_, global) = untilImplVerify("impl8.tchdl")

    assert(global.repo.error.counts == 0, showErrors(global))
  }

  test("complicated conflict verification. This cause error because of implementation of I0 for ST[T]") {
    val (_, global) = untilImplVerify("impl9.tchdl")

    assert(global.repo.error.counts == 1, showErrors(global))
    val err = global.repo.error.elems.head
    assert(err.isInstanceOf[Error.ImplementInterfaceConflict], showErrors(global))
  }

  test("impl for type parameter as target. this does not cause error") {
    val (_, global) = untilImplVerify("impl10.tchdl")

    assert(global.repo.error.counts == 0, showErrors(global))
  }

  test("impl for type parameter as target. this causes implement conflict error") {
    val (_, global) = untilImplVerify("impl11.tchdl")

    assert(global.repo.error.counts == 1, showErrors(global))
    val err = global.repo.error.elems.head
    assert(err.isInstanceOf[Error.ImplementInterfaceConflict], showErrors(global))
  }

  test("impl for enum must not be conflict between two same trait target impl") {
    val (trees, global) = untilImplVerify("enumDef2.tchdl")
    expectNoError(global)

    val filename = buildName(rootDir, filePath, "enumDef2.tchdl")
    val tree = trees.find(_.filename.get == filename).get

    val enumDef = tree.topDefs.collectFirst{ case enum: EnumDef => enum }.get
    val traitDef = tree.topDefs.collectFirst{ case traitDef: InterfaceDef => traitDef }.get
    val impls = tree.topDefs.collect{ case impl: ImplementInterface => impl }

    assert(impls.length == 2)

    assert(impls.head.interface.symbol == traitDef.symbol)
    assert(impls.tail.head.interface.symbol == traitDef.symbol)

    assert(impls.head.target.symbol == enumDef.symbol)
    assert(impls.tail.head.target.symbol == enumDef.symbol)
  }

  test("implement enum must not conflict between two different type parameter type") {
    val (trees, global) = untilImplVerify("enumDef3.tchdl")
    expectNoError(global)

    val filename = buildName(rootDir, filePath, "enumDef3.tchdl")
    val tree = trees.find(_.filename.get == filename).get

    val enumDef = tree.topDefs.collectFirst{ case enum: EnumDef => enum }.get
    val impls = tree.topDefs.collect{ case impl: ImplementClass => impl }

    assert(impls.length == 2)

    assert(impls.head.target.symbol == enumDef.symbol)
    assert(impls.tail.head.target.symbol == enumDef.symbol)
  }

  test("implement enum conflict between Option[T] and Option[Int]") {
    val (_, global) = untilImplVerify("enumDef4.tchdl")
    expectError(1)(global)

    val err = global.repo.error.elems.head
    assert(err.isInstanceOf[Error.ImplementClassConflict])
  }

  test("implement enum conflict between Option[T] and Option[T]") {
    val (_, global) = untilImplVerify("enumDef5.tchdl")
    expectError(1)(global)

    val err = global.repo.error.elems.head
    assert(err.isInstanceOf[Error.ImplementClassConflict])
  }
}
