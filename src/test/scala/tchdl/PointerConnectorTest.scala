package tchdl

import tchdl.parser._
import tchdl.typecheck._
import tchdl.backend._
import tchdl.ast._
import tchdl.util.GlobalData
import tchdl.backend.ast.{BackendLIR => lir}

class PointerConnectorTest extends TchdlFunSuite {
  def parse(filename: String): CompilationUnit =
    parseFile(_.compilation_unit)((gen, tree) => gen(tree, filename))(filename).asInstanceOf[CompilationUnit]

  def untilThisPhase(pkgName: Vector[String], module: String, names: String*): (Vector[PointerConnection], GlobalData) = {
    val fullnames = names.map(buildName(rootDir, filePath, _))
    val filenames = fullnames ++ builtInFiles

    val trees = filenames.map(parse)
    val moduleTree = parseString(_.`type`)((gen, tree) => gen.typeTree(tree)(Filename("")))(module).asInstanceOf[TypeTree]
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
    expectNoError(newGlobal)

    val lirModules = BackendLIRGen.exec(moduleContainers, methodContainers)
    val topModuleTpe = moduleContainers.head.tpe
    val connections = PointerConnector.exec(topModuleTpe, lirModules)

    (connections, newGlobal)
  }

  test("pointer connection for simple proc") {
    val (connections, global) = untilThisPhase(Vector("test"), "UseDeref", "procDeref.tchdl")
    assert(connections.length == 1)
    val connect = connections.head
    assert(connect.source.modulePath == Vector.empty)
    assert(connect.source.component == HierarchyComponent.Proc("multCycle", "init"))
    assert(connect.dest.length == 1)
    val dest = connect.dest.head
    assert(dest.modulePath == Vector.empty)
    assert(dest.component.isInstanceOf[HierarchyComponent.Deref])
    assert(dest.component.asInstanceOf[HierarchyComponent.Deref].ref.tpe == BackendType.bitTpe(8)(global))
  }
}
