package tchdl

import tchdl.ast.CompilationUnit
import tchdl.ast.TypeTree
import tchdl.{ast => frontend}
import tchdl.util._
import tchdl.backend._
import tchdl.backend.ast._
import tchdl.typecheck._

class BackendIRGenTest extends TchdlFunSuite {
  def parse(filename: String): CompilationUnit =
    parseFile(_.compilation_unit)((gen, tree) => gen(tree, filename))(filename).asInstanceOf[CompilationUnit]

  def untilThisPhase(pkgName: Vector[String], module: String, names: String*): (Vector[ModuleContainer], Vector[MethodContainer], GlobalData) = {
    val fullnames = names.map(buildName(rootDir, filePath, _))
    val filenames = fullnames ++ builtInFiles

    val trees = filenames.map(parse)
    val moduleTree = parseString(_.`type`)((gen, tree) => gen.typeTree(tree))(module).asInstanceOf[TypeTree]
    implicit val global: GlobalData = GlobalData(pkgName, moduleTree)

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
    val modules = BuildGeneratedModuleList.exec(newGlobal)
    expectNoError(newGlobal)

    val (moduleContainers, methodContainers) = BackendIRGen.exec(modules)(newGlobal)
    (moduleContainers, methodContainers, newGlobal)
  }

  test("simple module structure should be generate two module containers") {
    val (modules, methods, global) = untilThisPhase(Vector("test"), "Top", "simpleStructure.tchdl")
    val filename = buildName(rootDir, filePath, "simpleStructure.tchdl")
    val tree = global.compilationUnits.find(_.filename.get == filename).get

    assert(modules.length == 2)
    assert(methods.isEmpty)

    val topSymbol = tree.topDefs.find(_.symbol.name == "Top").map(_.symbol.asModuleSymbol).get
    val topTpe = BackendType(topSymbol, Vector.empty, Vector.empty)
    val top = modules.find(_.tpe == topTpe).get

    val subSymbol = tree.topDefs.find(_.symbol.name == "Sub").map(_.symbol.asModuleSymbol).get
    val subTpe = BackendType(subSymbol, Vector.empty, Vector.empty)

    assert(top.interfaces.isEmpty)
    assert(top.stages.isEmpty)
    assert(top.always.isEmpty)
    assert(top.fields.length == 1)

    val code = top.fields.head.code
    assert(code.length == 1)
    val construct = code.head
    assert(construct == backend.ast.ConstructModule(subTpe, Map.empty, Map.empty))
  }

  test("modules that have hardware parameters make two module containers with concrete hp values") {
    val (modules, methods, global) = untilThisPhase(Vector("test"), "Top[4]", "moduleWithHP0.tchdl")
    val filename = buildName(rootDir, filePath, "moduleWithHP0.tchdl")
    val tree = global.compilationUnits.find(_.filename.get == filename).get

    assert(modules.length == 2)
    assert(methods.isEmpty)

    val topSymbol = tree.topDefs.find(_.symbol.name == "Top").map(_.symbol.asModuleSymbol).get
    val topTpe = BackendType(topSymbol, Vector(HPElem.Num(4)), Vector.empty)
    val top = modules.find(_.tpe == topTpe).get

    val subSymbol = tree.topDefs.find(_.symbol.name == "Sub").map(_.symbol.asModuleSymbol).get
    val subTpe = BackendType(subSymbol, Vector(HPElem.Num(4)), Vector.empty)
    val sub = modules.find(_.tpe == subTpe).get

    assert(top.interfaces.length == 1)
    assert(top.fields.length == 1)
    assert(sub.interfaces.length == 1)

    val function = top.interfaces.head
    val add = sub.interfaces.head

    val functionParamA = findMethodTree(function.label.symbol, global).flatMap(_.params.find(_.name == "a")).map(_.symbol.path).get
    val functionParamB = findMethodTree(function.label.symbol, global).flatMap(_.params.find(_.name == "b")).map(_.symbol.path).get
    val bit = global.builtin.types.lookup("Bit")
    val bit4 = BackendType(bit, Vector(HPElem.Num(4)), Vector.empty)

    assert(function.code == Vector(
      Temp("TEMP_2", subTpe, ReferField(Term.This, "sub", subTpe)),
      Temp("TEMP_0", bit4, Ident(Term.Variable(functionParamA, bit4), bit4)),
      Temp("TEMP_1", bit4, Ident(Term.Variable(functionParamB, bit4), bit4)),
      CallInterface(add.label, Term.Node("TEMP_2", subTpe), Vector(Term.Node("TEMP_0", bit4), Term.Node("TEMP_1", bit4)), bit4)
    ))
  }

  test("build ALU circuit description should generate code correctly") {
    val (modules, methods, global) = untilThisPhase(Vector("test", "alu"), "Top", "ALU.tchdl")
    val aluFile = buildName(rootDir, filePath, "ALU.tchdl")
    val aluCU = global.compilationUnits.find(_.filename.get == aluFile).get

    assert(modules.length == 2)
    assert(methods.length == 2)

    val impls = aluCU.topDefs.collect { case impl: frontend.ImplementInterface => impl }
    val add = impls.flatMap(_.methods.find(_.name == "add")).map(_.symbol.asMethodSymbol).head
    val sub = impls.flatMap(_.methods.find(_.name == "sub")).map(_.symbol.asMethodSymbol).head

    assert(methods.exists(_.label.symbol == add))
    assert(methods.exists(_.label.symbol == sub))
  }
}
