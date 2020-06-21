package tchdl

import tchdl.util._
import tchdl.ast._
import tchdl.typecheck._
import tchdl.backend._

class BuildModuleListTest extends TchdlFunSuite {
  def parse(filename: String): CompilationUnit =
    parseFile(_.compilation_unit)((gen, tree) => gen(tree, filename))(filename).asInstanceOf[CompilationUnit]

  def untilThisPhase(pkgRoute: Vector[String], module: String, names: String*): (Seq[CompilationUnit], Vector[BuiltModule], GlobalData) = {
    implicit val global: GlobalData = new GlobalData
    val moduleTree = parseString(_.`type`)((gen, tree) => gen.typeTree(tree))(module).asInstanceOf[TypeTree]
    global.command.topModulePkg = pkgRoute
    global.command.topModule = Some(moduleTree)

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

    val trees0 = trees.map(TopDefTyper.exec)
    expectNoError

    trees0.foreach(ImplMethodSigTyper.exec)
    expectNoError

    val trees1 = trees0.map(Typer.exec)
    expectNoError

    trees1.foreach(RefCheck.exec)
    expectNoError

    val list = BuildGeneratedModuleList.exec.getOrElse(Vector.empty)
    val cus = trees1.filter(cu => files.contains(cu.filename.get))
    (cus, list, global)
  }

  test("top and one sub module, this should generate list correctly") {
    val (_, modules, global) = untilThisPhase(Vector("test"), "Top", "simpleStructure.tchdl")
    expectNoError(global)

    assert(modules.length == 2)

    val top = modules(0)
    val sub = modules(1)

    assert(top.childIDs.length == 1)
    assert(top.childIDs.head == sub.id)
    assert(top.impl.isDefined)
    assert(sub.impl.isEmpty)
  }

  test("top and one sub module with hardware parameter should compile correctly") {
    val (Seq(tree), modules, global) = untilThisPhase(Vector("test"), "Top[4]", "moduleWithHP0.tchdl")
    expectNoError(global)

    assert(modules.length == 2)

    val top = modules(0)
    val sub = modules(1)

    assert(top.module.hardwareParam.head == IntLiteral(4))
    assert(sub.module.hardwareParam.head == IntLiteral(4))
  }

  test("when constructing exactly same type, use same module's id") {
    val (Seq(tree), modules, global) = untilThisPhase(Vector("test"), "Top", "moduleWithSomeSubs.tchdl")
    expectNoError(global)

    assert(modules.length == 3)

    val subMod = tree.topDefs.collectFirst{ case mod: ModuleDef if mod.name == "Sub" => mod }.get
    val sub4Tpe = Type.RefType(subMod.symbol.asTypeSymbol, Vector(IntLiteral(4)), Vector.empty)
    val sub8Tpe = Type.RefType(subMod.symbol.asTypeSymbol, Vector(IntLiteral(8)), Vector.empty)

    val top  = modules(0)
    val sub4 = modules.find(_.module =:= sub4Tpe).get
    val sub8 = modules.find(_.module =:= sub8Tpe).get

    assert(top.childIDs.count(_ == sub4.id) == 2)
    assert(top.childIDs.count(_ == sub8.id) == 1)
  }
}
