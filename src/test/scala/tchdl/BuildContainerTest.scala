package tchdl

import tchdl.ast._
import tchdl.util._
import tchdl.typecheck._

class BuildContainerTest extends TchdlFunSuite {
  def parse(filename: String): CompilationUnit =
    parseFile(_.compilation_unit)((gen, tree) => gen(tree, filename))(filename).asInstanceOf[CompilationUnit]

  def untilBuild(names: String*): (Seq[CompilationUnit], GlobalData) = {
    implicit val global: GlobalData = GlobalData()
    val filename = names.map(buildName(rootDir, filePath, _))
    val filenames = filename ++ builtInFiles
    val trees = filenames.map(parse)

    trees.foreach(Namer.exec)
    assert(global.repo.error.counts == 0, global.repo.error.elems.mkString("\n"))

    trees.foreach(NamerPost.exec)
    assert(global.repo.error.counts == 0, global.repo.error.elems.mkString("\n"))

    trees.foreach(BuildImplContainer.exec)

    val cus = trees.filter(cu => filename.contains(cu.filename.get))
    (cus, global)
  }

  test("struct bounds miss match type between Num and Str") {
    val (_, global) = untilBuild("typeCheckHP0.tchdl")

    assert(global.repo.error.counts == 1, showErrors(global))
    val err = global.repo.error.elems.head
    assert(err.isInstanceOf[Error.TypeMismatch], showErrors(global))
  }

  test("interface impl's hardware parameter miss match type between Num and Str") {
    val (_, global) = untilBuild("typeCheckHP1.tchdl")

    assert(global.repo.error.counts == 1, showErrors(global))
    val err = global.repo.error.elems.head
    assert(err.isInstanceOf[Error.TypeMismatch], showErrors(global))
  }

  test("verify impl's type tree has type") {
    val (Seq(tree), global) = untilBuild("impl12.tchdl")
    expectNoError(global)

    val struct = tree.topDefs.collectFirst{ case s: StructDef => s }.get
    val interface = tree.topDefs.collectFirst{ case i: InterfaceDef => i }.get
    val implClass = tree.topDefs.collectFirst{ case impl: ImplementClass => impl }.get
    val implInterface = tree.topDefs.collectFirst{ case impl: ImplementInterface => impl }.get

    // verify no exception raised
    val cTargetTpe = implClass.target.tpe
    val iTargetTpe = implInterface.target.tpe
    val iInterfaceTpe = implInterface.interface.tpe

    assert(cTargetTpe == Type.RefType(struct.symbol.asTypeSymbol))
    assert(iTargetTpe == Type.RefType(struct.symbol.asTypeSymbol))
    assert(iInterfaceTpe == Type.RefType(interface.symbol.asInterfaceSymbol))
  }

  test("verify type parameter length mismatch in bounds") {
    val (_, global) = untilBuild("boundParams0.tchdl")
    expectError(1)(global)

    val err = global.repo.error.elems.head
    assert(err.isInstanceOf[Error.TypeParameterLengthMismatch])
  }

  test("append modifier into module's field symbols correctly") {
    val (Seq(tree), _) = untilBuild("parentSibling.tchdl")
    val module = tree.topDefs.collect{ case m: ModuleDef => m }.find(_.name == "M").get

    module.parents.foreach(parent => assert(parent.symbol.hasFlag(Modifier.Parent)))
    module.siblings.foreach(sibling => assert(sibling.symbol.hasFlag(Modifier.Sibling)))
  }
}
