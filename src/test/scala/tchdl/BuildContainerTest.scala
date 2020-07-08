package tchdl

import tchdl.ast._
import tchdl.util._
import tchdl.typecheck._

class BuildContainerTest extends TchdlFunSuite {
  def parse(filename: String): CompilationUnit =
    parseFile(_.compilation_unit)((gen, tree) => gen(tree, filename))(filename).asInstanceOf[CompilationUnit]

  def untilThisPhase(names: String*): (Seq[CompilationUnit], GlobalData) = {
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
    val (_, global) = untilThisPhase("typeCheckHP0.tchdl")

    assert(global.repo.error.counts == 1, showErrors(global))
    val err = global.repo.error.elems.head
    assert(err.isInstanceOf[Error.TypeMismatch], showErrors(global))
  }

  test("interface impl's hardware parameter miss match type between Num and Str") {
    val (_, global) = untilThisPhase("typeCheckHP1.tchdl")

    assert(global.repo.error.counts == 1, showErrors(global))
    val err = global.repo.error.elems.head
    assert(err.isInstanceOf[Error.TypeMismatch], showErrors(global))
  }

  test("verify impl's type tree has type") {
    val (Seq(tree), global) = untilThisPhase("impl12.tchdl")
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
    val (_, global) = untilThisPhase("boundParams0.tchdl")
    expectError(1)(global)

    val err = global.repo.error.elems.head
    assert(err.isInstanceOf[Error.TypeParameterLengthMismatch])
  }

  test("append modifier into module's field symbols correctly") {
    val (Seq(tree), _) = untilThisPhase("parentSibling.tchdl")
    val module = tree.topDefs.collect{ case m: ModuleDef => m }.find(_.name == "M").get

    module.parents.foreach(parent => assert(parent.symbol.hasFlag(Modifier.Parent)))
    module.siblings.foreach(sibling => assert(sibling.symbol.hasFlag(Modifier.Sibling)))
  }

  test("implement enum must be done correctly") {
    val (Seq(tree), global) = untilThisPhase("enumOptionImpl0.tchdl")
    expectNoError(global)

    val enumImpl = tree.topDefs.collectFirst{ case impl: ImplementClass => impl }.get
    val enumDef = tree.topDefs.collectFirst{ case enum: EnumDef => enum }.get

    assert(enumImpl.target.symbol == enumDef.symbol)
  }

  test("implement enum's trait must be done correctly") {
    val (Seq(tree), global) = untilThisPhase("enumDef1.tchdl")
    expectNoError(global)

    val traitDef = tree.topDefs.collectFirst{ case traitDef: InterfaceDef => traitDef }.get
    val enumDef = tree.topDefs.collectFirst{ case enumDef: EnumDef => enumDef }.get
    val implDef = tree.topDefs.collectFirst{ case impl: ImplementInterface => impl }.get

    assert(implDef.interface.symbol == traitDef.symbol)
    assert(implDef.target.symbol == enumDef.symbol)
  }

  test("use another package type") {
    val (trees, global) = untilThisPhase("UseAnotherPackageType.tchdl", "TypeSource.tchdl")
    expectNoError(global)

    val cu = trees.find(_.filename.get.contains("UseAnotherPackageType.tchdl")).get
    val impl = cu.topDefs
      .collectFirst{ case impl: ImplementClass if impl.target.expr.isInstanceOf[SelectPackage] => impl }
      .get

    val source = trees.find(_.filename.get.contains("TypeSource.tchdl")).get
    val ST1 = source.topDefs.collectFirst{ case struct: StructDef => struct }.get

    assert(impl.target.tpe.isInstanceOf[Type.RefType])
    assert(impl.target.tpe.asRefType.origin == ST1.symbol)
  }

  test("name conflict for struct's field") {
    val (_, global) = untilThisPhase("NameConflict0.tchdl")
    expectError(1)(global)

    val err = global.repo.error.elems.head
    assert(err.isInstanceOf[Error.DefinitionNameConflict])
  }

  test("name conflict for module's field") {
    val (_, global) = untilThisPhase("NameConflict1.tchdl")
    expectError(1)(global)

    val err = global.repo.error.elems.head
    assert(err.isInstanceOf[Error.DefinitionNameConflict])
  }

  test("name conflict of interfaces") {
    val (_, global) = untilThisPhase("NameConflict2.tchdl")
    expectError(1)(global)

    val err = global.repo.error.elems.head
    assert(err.isInstanceOf[Error.DefinitionNameConflict])
  }
}
