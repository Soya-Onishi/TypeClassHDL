package tchdl

import tchdl.util._
import tchdl.ast._
import tchdl.typecheck._
import tchdl.backend._
import tchdl.parser.Filename

class BuildModuleListTest extends TchdlFunSuite {
  def parse(filename: String): CompilationUnit =
    parseFile(_.compilation_unit)((gen, tree) => gen(tree, filename))(filename).asInstanceOf[CompilationUnit]

  def untilThisPhase(pkgRoute: Vector[String], module: String, names: String*): (Seq[CompilationUnit], Vector[BuiltModule], GlobalData) = {
    val moduleTree = parseString(_.`type`)((gen, tree) => gen.typeTree(tree)(Filename("")))(module).asInstanceOf[TypeTree]

    val files = names.map(buildName(rootDir, filePath, _))
    val filenames = files ++ builtInFiles
    val trees = filenames.map(parse)

    implicit val global: GlobalData = GlobalData(pkgRoute, moduleTree)

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

    val newGlobal = global.assignCompilationUnits(trees1.toVector)
    val list = BuildGeneratedModuleList.exec(newGlobal)
    val cus = trees1.filter(cu => files.contains(cu.filename))
    (cus, list, newGlobal)
  }

  test("top and one sub module, this should generate list correctly") {
    val (_, modules, global) = untilThisPhase(Vector("test"), "Top", "simpleStructure.tchdl")
    expectNoError(global)

    assert(modules.length == 2)

    val top = modules(0)
    val sub = modules(1)

    assert(top.impl.length == 1)
    assert(sub.impl.isEmpty)
  }

  test("top and one sub module with hardware parameter should compile correctly") {
    val (Seq(tree), modules, global) = untilThisPhase(Vector("test"), "Top[4]", "moduleWithHP0.tchdl")
    expectNoError(global)

    assert(modules.length == 2)

    val top = modules(0)
    val sub = modules(1)

    assert(top.tpe.hargs.head == HPElem.Num(4))
    assert(sub.tpe.hargs.head == HPElem.Num(4))
  }

  test("when constructing exactly same type, use same module's id") {
    val (Seq(tree), modules, global) = untilThisPhase(Vector("test"), "Top", "moduleWithSomeSubs.tchdl")
    expectNoError(global)

    assert(modules.length == 3)

    val subMod = tree.topDefs.collectFirst{ case mod: ModuleDef if mod.name == "Sub" => mod }.get
    val sub4Tpe = BackendType(subMod.symbol.asTypeSymbol, Vector(HPElem.Num(4)), Vector.empty, isPointer = false)
    val sub8Tpe = BackendType(subMod.symbol.asTypeSymbol, Vector(HPElem.Num(8)), Vector.empty, isPointer = false)

    val tpes = modules.map(_.tpe)
    assert(tpes.contains(sub4Tpe))
    assert(tpes.contains(sub8Tpe))
  }
}
