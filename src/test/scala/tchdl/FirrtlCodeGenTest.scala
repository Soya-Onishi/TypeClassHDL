package tchdl

import tchdl.ast._
import tchdl.backend.ast.{BackendLIR => lir}
import tchdl.util._
import tchdl.typecheck._
import tchdl.parser._
import tchdl.backend._

import firrtl.{ir => fir}

class FirrtlCodeGenTest extends TchdlFunSuite {
  def parse(filename: String): CompilationUnit =
    parseFile(_.compilation_unit)((gen, tree) => gen(tree, filename))(filename).asInstanceOf[CompilationUnit]

  def untilThisPhase(pkgName: Vector[String], module: String, names: String*): (fir.Circuit, GlobalData) = {
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

    val topModule = lirModules.find(_.tpe == topModuleTpe).get
    val circuit = FirrtlCodeGen.exec(topModule, lirModules, connections)(newGlobal)

    (circuit, newGlobal)
  }

  test("simple code") {
    val (circuit, _) = untilThisPhase(Vector("test"), "Top[8]", "OnlyTopThrowWire.tchdl")
    val modules = circuit.modules.collect{ case m: fir.Module => m }

    assert(modules.length == 1)

    val top = modules.head
    val stmts = top.body.asInstanceOf[fir.Block].stmts
    val whens = stmts.collect{ case w: fir.Conditionally => w }

    assert(whens.length == 1)

    val when = whens.head
    assert(when.pred.isInstanceOf[fir.Reference])
    val active = when.pred.asInstanceOf[fir.Reference]
    assert(active.name.matches("function_[0-9a-f]+\\$_active"))
    assert(top.ports.exists(_.name == active.name))
    val conseq = when.conseq.asInstanceOf[fir.Block].stmts
    val connects = conseq.collect{ case c: fir.Connect => c }
    assert(connects.length == 1)
    val connect = connects.head

    val dst = connect.loc.asInstanceOf[fir.Reference]
    val src = connect.expr.asInstanceOf[fir.Reference]

    assert(dst.name.matches("function_[0-9a-f]+\\$_ret"))
    assert(src.name.matches("function_[0-9a-f]+\\$in"), src.name)
  }

  test("use proc and deref") {
    val (circuit, _) = untilThisPhase(Vector("test"), "UseDeref", "procDeref.tchdl")
    val modules = circuit.modules.collect{ case m: fir.Module => m }
    val top = modules.head
    val stmts = top.body.asInstanceOf[fir.Block].stmts
    val whens = stmts.collect{ case w: fir.Conditionally => w }

    assert(whens.length == 3)

    val exec = whens.find{ when =>
      val ref = when.pred.asInstanceOf[fir.Reference]
      ref.name.matches("exec_[0-9a-f]+\\$_active")
    }.get

    val conseq = exec.conseq.asInstanceOf[fir.Block].stmts
    val connects = conseq.collect{ case c: fir.Connect => c }

    // test deref
    val connect = connects.find(_.loc.asInstanceOf[fir.Reference].name.matches("exec_[0-9a-f]+\\$_ret")).get
    val srcName = connect.expr.asInstanceOf[fir.Reference].name
    val nodes = exec.conseq.asInstanceOf[fir.Block].stmts.collect{ case n: fir.DefNode => n }
    val primNode = nodes.find(_.name == srcName).get

    val doPrim = primNode.value.asInstanceOf[fir.DoPrim]
    assert(doPrim.op == firrtl.PrimOps.Add)
    val arg = doPrim.args.head.asInstanceOf[fir.Reference]

    val argNode = nodes.find(_.name == arg.name).get
    val betweenRef = argNode.value.asInstanceOf[fir.Reference]
    val pointerNode = nodes.find(_.name == betweenRef.name).get

    assert(pointerNode.value.asInstanceOf[fir.Reference].name == "__pointer_0")

    // test return
    val multCycleBlock = whens(2).conseq.asInstanceOf[fir.Block].stmts
    val whenConnect = multCycleBlock.collectFirst{ case c: fir.Conditionally => c }.get
    val pointerConnect = whenConnect.conseq.asInstanceOf[fir.Connect]

    pointerConnect.expr.asInstanceOf[fir.Reference].name.matches("multCycle_[0-9a-f]+_next\\$result")
  }

  test("use multiple proc") {
    def checkID(stmts: Seq[fir.Statement], id: Int): Unit = {
      val nodes = stmts.collect{ case n: fir.DefNode => n }
      val connects = stmts.collect{ case c: fir.Connect => c }
      val retConnect = connects.find(_.loc == fir.Reference("_IFRET_0", fir.UIntType(fir.IntWidth(1)))).get
      val srcName = retConnect.expr.asInstanceOf[fir.Reference].name
      val node = nodes.find(_.name == srcName).get
      assert(node.value.isInstanceOf[fir.UIntLiteral])
      assert(node.value.asInstanceOf[fir.UIntLiteral].value == id)
    }

    val (circuit, global) = untilThisPhase(Vector("test"), "Top", "procTwoProcOneDeref.tchdl")

    val module = circuit.modules.head.asInstanceOf[fir.Module]
    val stmts = module.body.asInstanceOf[fir.Block].stmts
    val whens = stmts.collect{ case w: fir.Conditionally => w }
    assert(whens.length == 5)

    val exec = whens.head
    assert(exec.pred.isInstanceOf[fir.Reference])
    assert(exec.pred.asInstanceOf[fir.Reference].name.matches("exec_[0-9a-f]+\\$_active"))

    val execStmts = exec.conseq.asInstanceOf[fir.Block].stmts
    val execNodes = execStmts.collect{ case n: fir.DefNode => n }
    val muxNodes = execNodes.filter(_.value.isInstanceOf[fir.Mux])
    assert(muxNodes.length == 1)
    val muxNode = muxNodes.head
    val mux = muxNode.value.asInstanceOf[fir.Mux]
    assert(mux.fval.isInstanceOf[fir.Reference])
    val condOps = mux.cond.asInstanceOf[fir.DoPrim]
    val condRef = condOps.args.head.asInstanceOf[fir.Reference]
    val condNode = execNodes.find(_.name == condRef.name).get
    val pointerName = condNode.value.asInstanceOf[fir.Reference].name
    assert(pointerName.matches("exec_[0-9a-f]+\\$0\\$pointer_0"))

    val execIFs = execStmts.collect{ case c: fir.Conditionally => c }
    assert(execIFs.length == 1)
    val execIF = execIFs.head
    checkID(execIF.conseq.asInstanceOf[fir.Block].stmts, 0)
    checkID(execIF.alt.asInstanceOf[fir.Block].stmts, 1)

    val twoProcFirstStmts = whens(3).conseq.asInstanceOf[fir.Block].stmts
    val twoProcFirstConnects = twoProcFirstStmts.collect{ case c: fir.Connect => c }
    val idConnect = twoProcFirstConnects.find(_.loc.asInstanceOf[fir.Reference].name.matches("twoProc_[0-9a-f]+_second\\$_id")).get
    assert(idConnect.expr.asInstanceOf[fir.Reference].name.matches("twoProc_[0-9a-f]+_first\\$_id"))
  }

  test("proc from sibling") {
    val (circuit, global) = untilThisPhase(Vector("test"), "Top", "procFromSibling.tchdl")
    val top = circuit.modules.find(_.name == "Top").get.asInstanceOf[fir.Module]
    val sub0 = circuit.modules.find(_.name == "Top_sub0").get.asInstanceOf[fir.Module]
    val sub1 = circuit.modules.find(_.name == "Top_sub1").get.asInstanceOf[fir.Module]

    // In Top
    val topStmts = top.body.asInstanceOf[fir.Block].stmts
    val topWires = topStmts.collect{ case w: fir.DefWire => w }
    val topPointerWire = topWires.find(_.name == "__pointer_0").get
    val bit4 = fir.UIntType(fir.IntWidth(4))
    assert(topPointerWire.tpe == bit4)
    val topConnects = topStmts.collect{ case c: fir.Connect => c }
    val passToPointer = topConnects.find(_.loc == fir.Reference("__pointer_0", fir.UnknownType)).get
    val passFromPointer = topConnects.find(_.expr == fir.Reference("__pointer_0", fir.UnknownType)).get

    // In Sub0
    def subXRef(n: Int) = fir.Reference(s"sub$n", fir.UnknownType)
    assert(passToPointer.expr == fir.SubField(subXRef(1), "_pointer_0", fir.UnknownType))
    assert(passFromPointer.loc == fir.SubField(subXRef(0), "_pointer_0", fir.UnknownType))

    val sub0Stmts = sub0.body.asInstanceOf[fir.Block].stmts
    val function = sub0Stmts.collectFirst{ case c: fir.Conditionally => c }.get
    val functionStmts = function.conseq.asInstanceOf[fir.Block].stmts
    val fnodes = functionStmts.collect{ case n: fir.DefNode => n }
    val fnode = fnodes.find(_.value == fir.Reference("__pointer_0", fir.UnknownType)).get
    val fconnects = functionStmts.collect{ case c: fir.Connect => c }
    val fconnect = fconnects.find(c => c.loc.isInstanceOf[fir.Reference] && c.loc.asInstanceOf[fir.Reference].name.matches("function_[0-9a-f]+\\$_ret")).get
    assert(fconnect.expr == fir.Reference(fnode.name, bit4))

    val sub0Connects = sub0Stmts.collect{ case c: fir.Connect => c }
    val sub0PConnect = sub0Connects.collect{ case c @ fir.Connect(_, fir.Reference("__pointer_0", _), fir.Reference("_pointer_0", _)) => c }
    assert(sub0PConnect.length == 1)
    val sub0Wires = sub0Stmts.collect{ case w @ fir.DefWire(_, "__pointer_0", _) => w }
    assert(sub0Wires.length == 1)

    // In Sub1
    val sub1Stmts = sub1.body.asInstanceOf[fir.Block].stmts
    val sub1Ports = sub1.ports
    val sub1Wires = sub1Stmts.collect{ case w: fir.DefWire => w }
    val sub1PWires = sub1Wires.collect{ case w @ fir.DefWire(_, "__pointer_0", _) => w }
    assert(sub1PWires.length == 1)
    val sub1PPorts = sub1Ports.collect{ case p @ fir.Port(_, "_pointer_0", fir.Output, _) => p }
    assert(sub1PPorts.length == 1)
  }

  test("proc from parent") {
    val (circuit, global) = untilThisPhase(Vector("test"), "Top", "procFromIndParent.tchdl")
    val sub = circuit.modules.find(_.name == "Top_sub").get.asInstanceOf[fir.Module]
    val port = sub.ports.find(_.name == "_pointer_0")
    assert(port.isDefined)
    val subStmts = sub.body.asInstanceOf[fir.Block].stmts
    val subConnects = subStmts.collect{ case c: fir.Connect => c }
    val fromParent = subConnects.collectFirst{ case c @ fir.Connect(_, _, fir.Reference("_pointer_0", _)) => c }.get
    val toSubSub = subConnects.collectFirst{ case c @ fir.Connect(_, _, fir.Reference("__pointer_0", _)) => c }.get

    val subsub = fir.Reference("subsub", fir.UnknownType)
    assert(fromParent.loc == fir.Reference("__pointer_0", fir.UnknownType))
    assert(toSubSub.loc == fir.SubField(subsub, "_pointer_0", fir.UnknownType))
  }

  test("deref from same proc to multiple module") {
    val (circuit, global) = untilThisPhase(Vector("test"), "Top", "procDerefAtMultModule.tchdl")
    val top = circuit.modules.find(_.name == "Top").get.asInstanceOf[fir.Module]
    val topStmts = top.body.asInstanceOf[fir.Block].stmts
    val wires = topStmts.collect{ case w: fir.DefWire => w }
    assert(wires.exists(_.name == "__pointer_0"))
    val connects = topStmts.collect{ case c: fir.Connect => c }
    val toWires = connects.collect{ case c @ fir.Connect(_, fir.Reference(name, _), _) if name == "__pointer_0" => c }
    val fromWires = connects.collect{ case c @ fir.Connect(_, _, fir.Reference(name, _)) if name == "__pointer_0" => c }

    assert(toWires.length == 1)
    assert(fromWires.length == 2)

    val toWire = toWires.head
    def subxRef(n: Int) = fir.Reference(s"sub$n", fir.UnknownType)
    assert(toWire.expr == fir.SubField(subxRef(0), "_pointer_0", fir.UnknownType))
    assert(fromWires(0).loc == fir.SubField(subxRef(1), "_pointer_0", fir.UnknownType))
    assert(fromWires(1).loc == fir.SubField(subxRef(2), "_pointer_0", fir.UnknownType))
  }

  test("elaborate stage") {
    val (circuit, global) = untilThisPhase(Vector("test"), "Top", "stageMultCycle.tchdl")
    val top = circuit.modules.find(_.name == "Top").get.asInstanceOf[fir.Module]
    val topStmts = top.body.asInstanceOf[fir.Block].stmts
    val regs = topStmts.collect{ case r: fir.DefRegister => r }
    assert(regs.length == 5)

    val outputs = top.ports.filter(_.direction == fir.Output)
    assert(outputs.length == 1)
    assert(outputs.head.name == "outport")

    val topWhens = topStmts.collect{ case c: fir.Conditionally => c}
    assert(topWhens.length == 2)

    val execStmts = topWhens(0).conseq.asInstanceOf[fir.Block].stmts
    val execConnects = execStmts.collect{ case c: fir.Connect => c }
    assert(execConnects.length == 4)
    val connectValue0 = execConnects.collectFirst{ case c @ fir.Connect(_, fir.Reference(name, _), _) if name.matches("st_[0-9a-f]+\\$s1\\$value0") => c }
    assert(connectValue0.isDefined)

    val stStmts = topWhens(1).conseq.asInstanceOf[fir.Block].stmts
    val stWhens = stStmts.collect{ case c: fir.Conditionally => c }
    val s2Stmts = stWhens(1).conseq.asInstanceOf[fir.Block].stmts
    val s2Connects = s2Stmts.collect{ case c: fir.Connect => c }
    assert(s2Connects.length == 2)
    val connectPort = s2Connects.head
    assert(connectPort.loc == fir.Reference("outport", fir.UIntType(fir.IntWidth(2))))
    assert(connectPort.expr.asInstanceOf[fir.Reference].name.matches("st_[0-9a-f]+\\$s2\\$value2"))
  }
}
