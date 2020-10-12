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

  def untilThisPhase(pkgName: Vector[String], module: String, names: String*): (Vector[PointerConnection], Vector[lir.Module], GlobalData) = {
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

    (connections, lirModules, newGlobal)
  }

  test("pointer connection for simple proc") {
    val (connections, _, global) = untilThisPhase(Vector("test"), "UseDeref", "procDeref.tchdl")
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

  test("multiple same commence proc") {
    val (connections, modules, _) = untilThisPhase(Vector("test"), "Top", "procMultiDeref.tchdl")
    val top = findModule(modules, "Top").get
    val nodes = findAllComponents[lir.Node](top.procedures)

    assert(connections.length == 1)
    val connect = connections.head
    assert(connect.source.modulePath == Vector.empty)
    assert(connect.dest.length == 2)
    assert(connect.dest.forall(_.component.isInstanceOf[HierarchyComponent.Deref]))
    val dest = connect.dest.map(_.component.asInstanceOf[HierarchyComponent.Deref].ref)
    val derefNode = dest.map(d => nodes.find(_.name == d.name).get)
    val nodeRef = derefNode.map(_.src.asInstanceOf[lir.Reference])
    assert(nodeRef(0).name.matches("exec0_[0-9a-f]+\\$0\\$pointer0_0"), nodeRef(0).name)
    assert(nodeRef(1).name.matches("exec1_[0-9a-f]+\\$0\\$pointer1_0"), nodeRef(1).name)
  }

  test("two proc and one deref") {
    val (connections, modules, _) = untilThisPhase(Vector("test"), "Top", "procTwoProcOneDeref.tchdl")
    val top = findModule(modules, "Top").get
    val nodes = findAllComponents[lir.Node](top.procedures)

    assert(connections.length == 2)
    val oneProc = connections.find(_.source.component.asInstanceOf[HierarchyComponent.Proc].name == "oneProc").get
    val twoProc = connections.find(_.source.component.asInstanceOf[HierarchyComponent.Proc].name == "twoProc").get
    assert(oneProc.dest.length == 1)
    assert(twoProc.dest.length == 1)
    assert(oneProc.dest.head.component == twoProc.dest.head.component)

    val ref = oneProc.dest.head.component.asInstanceOf[HierarchyComponent.Deref].ref
    val pointerNode = nodes.find(_.name == ref.name).get
    assert(pointerNode.src.isInstanceOf[lir.Reference])
    assert(pointerNode.src.asInstanceOf[lir.Reference].name.matches("exec_[0-9a-f]+\\$0\\$pointer_0"))
  }

  test("use deref from submodule pointer") {
    val (connections, modules, _) = untilThisPhase(Vector("test"), "Top", "procFromSubModule.tchdl")
    val top = findModule(modules, "Top").get
    val node = findAllComponents[lir.Node](top.procedures)

    assert(connections.length == 1)
    val connect = connections.head
    assert(connect.dest.length == 1)
    val src = connect.source
    val dst = connect.dest.head

    assert(src.modulePath == Vector("sub"))
    assert(src.component == HierarchyComponent.Proc("multCycle", "first"))
    assert(dst.modulePath == Vector.empty)

    val derefRef = dst.component.asInstanceOf[HierarchyComponent.Deref].ref
    val derefNode = node.find(_.name == derefRef.name).get
    val srcName = derefNode.src.asInstanceOf[lir.Reference].name
    assert(srcName.matches("function_[0-9a-f]+\\$0\\$pointer_0"), srcName)
  }

  test("use deref from parent pointer") {
    val (connections, modules, _) = untilThisPhase(Vector("test"), "Top", "procFromParent.tchdl")
    val sub = findModule(modules, "Sub").get
    val nodes = findAllComponents[lir.Node](sub.procedures)

    assert(connections.length == 1)
    val connect = connections.head
    assert(connect.dest.length == 1)

    val src = connect.source
    val dst = connect.dest.head

    assert(src.modulePath == Vector.empty)
    assert(src.component == HierarchyComponent.Proc("multCycle", "first"))

    assert(dst.modulePath == Vector("sub"))
    val derefRef = dst.component.asInstanceOf[HierarchyComponent.Deref].ref
    val node = nodes.find(_.name == derefRef.name).get
    val refName = node.src.asInstanceOf[lir.Reference].name
    assert(refName.matches("function_[0-9a-f]+\\$pointer"))
  }

  test("use deref from sibling pointer") {
    val (connections, modules, _) = untilThisPhase(Vector("test"), "Top", "procFromSibling.tchdl")

    val sub0 = findModule(modules, "Sub0").get
    val nodes = findAllComponents[lir.Node](sub0.procedures)

    assert(connections.length == 1)
    val connect = connections.head
    assert(connect.dest.length == 1)

    val src = connect.source
    val dst = connect.dest.head

    assert(src.modulePath == Vector("sub1"))
    assert(src.component == HierarchyComponent.Proc("multCycle", "first"))
    assert(dst.modulePath == Vector("sub0"))

    val derefRef = dst.component.asInstanceOf[HierarchyComponent.Deref].ref
    val node = nodes.find(_.name == derefRef.name).get
    val refName = node.src.asInstanceOf[lir.Reference].name
    assert(refName.matches("function_[0-9a-f]+\\$0\\$pointer_0"))
  }

  test("use deref from indirect parent pointer") {
    val (connections, modules, _) = untilThisPhase(Vector("test"), "Top", "procFromIndParent.tchdl")

    val subsub = findModule(modules, "SubSub").get
    val nodes = findAllComponents[lir.Node](subsub.procedures)

    assert(connections.length == 1)
    val connect = connections.head
    assert(connect.dest.length == 1)

    val src = connect.source
    val dst = connect.dest.head

    assert(src.modulePath == Vector.empty)
    assert(src.component == HierarchyComponent.Proc("multCycle", "first"))
    assert(dst.modulePath == Vector("sub", "subsub"))

    val derefRef = dst.component.asInstanceOf[HierarchyComponent.Deref].ref
    val node = nodes.find(_.name == derefRef.name).get
    val refName = node.src.asInstanceOf[lir.Reference].name
    assert(refName.matches("caller_[0-9a-f]+\\$0\\$pointer_0"))
  }

  test("use deref via stage register") {
    val (connections, modules, _) = untilThisPhase(Vector("test"), "Top", "procDerefViaStage.tchdl")
    assert(connections.length == 1)
    val connect = connections.head
    assert(connect.dest.length == 1)

    val top = findModule(modules, "Top").get
    val nodes = findAllComponents[lir.Node](top.procedures)

    val src = connect.source
    val dst = connect.dest.head

    assert(src.modulePath == Vector.empty)
    assert(src.component == HierarchyComponent.Proc("multCycle", "first"))
    assert(dst.modulePath == Vector.empty)

    val derefRef = dst.component.asInstanceOf[HierarchyComponent.Deref].ref
    val node = nodes.find(_.name == derefRef.name).get
    val refName = node.src.asInstanceOf[lir.Reference].name
    assert(refName.matches("receiver_[0-9a-f]+\\$pointer"))
  }

  test("use memory read") {
    val (connections, modules, _) = untilThisPhase(Vector("test"), "Top", "useMemory.tchdl")
    assert(connections.length == 2)
    val memRead = connections(1)
    assert(memRead.dest.length == 1)
    assert(memRead.dest.head.component.isInstanceOf[HierarchyComponent.Deref])
    val component = memRead.dest.head.component
    val deref = component.asInstanceOf[HierarchyComponent.Deref]

    val nodeName = deref.ref.name
    val nodes = findAllComponents[lir.Node](modules.head.procedures)
    val node = nodes.find(_.name == nodeName).get
    assert(node.src.isInstanceOf[lir.Reference])
    assert(node.src.asInstanceOf[lir.Reference].name.matches("read_[0-9a-f]+\\$0\\$dataPointer_0"))
  }
}
