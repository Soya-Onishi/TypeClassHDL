package tchdl

import tchdl.ast._
import tchdl.backend.ast.{BackendLIR => lir}
import tchdl.util._
import tchdl.typecheck._
import tchdl.parser._
import tchdl.backend._

import firrtl.{ir => fir}

class FirrtlCodeGenTest extends TchdlFunSuite {
  def extractHashCode(regex: String, from: String): String = {
    val r = regex.r
    r.findAllIn(from).matchData.map{ _.group(1) }.toVector.head
  }

  def concatNames(function: String, code: String, remains: String*): String = {
    function + "_" + code + "$" + remains.mkString("$")
  }

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

    // test in init block
    val initStmts = whens(1).conseq.asInstanceOf[fir.Block].stmts
    val initConnects = initStmts.collect{ case c: fir.Connect => c }
    val idConnect = initConnects.collectFirst{ case c @ fir.Connect(_, fir.Reference(name, _), _) if name.matches("multCycle_[0-9a-f]+_next\\$_id") => c }.get
    assert(idConnect.loc.asInstanceOf[fir.Reference].name.matches("multCycle_[0-9a-f]+_next\\$_id"))
    assert(idConnect.expr.asInstanceOf[fir.Reference].name.matches("multCycle_[0-9a-f]+_init\\$_id"))

    // check whether there is registers that proc uses
    val regs = stmts.collect { case r: fir.DefRegister => r }
    assert(regs.length == 7)
    assert(regs.exists(_.name.matches("multCycle_[0-9a-f]+_init\\$operand0")))
    assert(regs.exists(_.name.matches("multCycle_[0-9a-f]+_init\\$operand1")))
    assert(regs.exists(_.name.matches("multCycle_[0-9a-f]+_next\\$result")))
    assert(regs.exists(_.name.matches("multCycle_[0-9a-f]+_init\\$_id")))
    assert(regs.exists(_.name.matches("multCycle_[0-9a-f]+_next\\$_id")))
    assert(regs.exists(_.name.matches("multCycle_[0-9a-f]+_init\\$_active")))
    assert(regs.exists(_.name.matches("multCycle_[0-9a-f]+_next\\$_active")))

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

  test("build most simple code") {
    val (circuit, _) = untilThisPhase(Vector("test"), "Top[8]", "OnlyTopThrowWire.tchdl")
    val top = circuit.modules.find(_.name == "Top").get.asInstanceOf[fir.Module]

    assert(top.ports.length == 3)
    assert(top.ports(0).name.matches("function_[0-9a-f]+\\$_active"))
    assert(top.ports(1).name.matches("function_[0-9a-f]+\\$in"))
    assert(top.ports(2).name.matches("function_[0-9a-f]+\\$_ret"))

    assert(top.ports(0).direction == fir.Input)
    assert(top.ports(1).direction == fir.Input)
    assert(top.ports(2).direction == fir.Output)

    val stmts = top.body.asInstanceOf[fir.Block].stmts
    val invalids = stmts.collect { case i: fir.IsInvalid => i }
    assert(invalids.length == 1)
    val invalid = invalids.head
    assert(invalid.expr.asInstanceOf[fir.Reference].name.matches("function_[0-9a-f]+\\$_ret"))
  }

  test("input interface with Unit return type") {
    val (circuit, _) = untilThisPhase(Vector("test", "inner"), "Top", "InputUnitFunction.tchdl")
    val top = circuit.modules.find(_.name == "Top").get.asInstanceOf[fir.Module]

    assert(top.ports.length == 1)
    assert(top.ports.head.name.matches("f_[0-9a-f]+\\$_active"))

    val topStmts = top.body.asInstanceOf[fir.Block].stmts
    assert(topStmts.length == 1)
    val when = topStmts.head.asInstanceOf[fir.Conditionally]
    assert(when.conseq.asInstanceOf[fir.Block].stmts.isEmpty)
  }

  test("module that has internal interface and call it") {
    val (circuit, global) = untilThisPhase(Vector("test"), "Top", "InputCallInternal.tchdl")
    val top = circuit.modules.find(_.name == "Top").get.asInstanceOf[fir.Module]

    assert(top.ports.length == 3)
    assert(top.ports(0).name.matches("inputFunc_[0-9a-f]+\\$_active"))
    assert(top.ports(1).name.matches("inputFunc_[0-9a-f]+\\$in"))
    assert(top.ports(2).name.matches("inputFunc_[0-9a-f]+\\$_ret"))

    val topStmts = top.body.asInstanceOf[fir.Block].stmts

    val wires = topStmts.collect{ case w: fir.DefWire => w }
    assert(wires.length == 3)
    assert(wires(0).name.matches("internalFunc_[0-9a-f]+\\$_active"))
    assert(wires(1).name.matches("internalFunc_[0-9a-f]+\\$x"))
    assert(wires(2).name.matches("internalFunc_[0-9a-f]+\\$_ret"))

    val invalids = topStmts.collect{ case i: fir.IsInvalid => i }
    assert(invalids.length == 3)

    val whens = topStmts.collect{ case c: fir.Conditionally => c }
    assert(whens.length == 2)
    val inputFunc = whens.head
    val internalFunc = whens.tail.head

    val fir.Reference(inputFuncPred, _) = inputFunc.pred
    val fir.Reference(internalFuncPred, _) = internalFunc.pred
    assert(inputFuncPred.matches("inputFunc_[0-9a-f]+\\$_active"))
    assert(internalFuncPred.matches("internalFunc_[0-9a-f]+\\$_active"))

    val inputFuncStmts = inputFunc.conseq.asInstanceOf[fir.Block].stmts
    assert(inputFuncStmts.length == 5)
    val Seq(paramNode, litNode, activate, assignArg, retConnect) = inputFuncStmts
    assert(paramNode.isInstanceOf[fir.DefNode])
    assert(paramNode.asInstanceOf[fir.DefNode].value.asInstanceOf[fir.Reference].name.matches("inputFunc_[0-9a-f]+\\$in"))
    assert(litNode.asInstanceOf[fir.DefNode].value.isInstanceOf[fir.UIntLiteral])
    val fir.Connect(_, activeDst: fir.Reference, _) = activate
    val fir.Connect(_, argDst: fir.Reference, argSrc: fir.Reference) = assignArg
    val fir.Connect(_, retDst: fir.Reference, retSrc: fir.Reference) = retConnect

    assert(activeDst.name.matches("internalFunc_[0-9a-f]+\\$_active"))
    assert(argDst.name.matches("internalFunc_[0-9a-f]+\\$x"))
    assert(argSrc.name == paramNode.asInstanceOf[fir.DefNode].name)
    assert(retDst.name.matches("inputFunc_[0-9a-f]+\\$_ret"))
    assert(retSrc.name.matches("internalFunc_[0-9a-f]+\\$_ret"))

    val internalFuncStmts = internalFunc.conseq.asInstanceOf[fir.Block].stmts
    assert(internalFuncStmts.length == 1)
    val Seq(fir.Connect(_, dst, src)) = internalFuncStmts
    val dstRef = dst.asInstanceOf[fir.Reference]
    val srcRef = src.asInstanceOf[fir.Reference]
    assert(dstRef.name.matches("internalFunc_[0-9a-f]+\\$_ret"))
    assert(srcRef.name.matches("internalFunc_[0-9a-f]+\\$x"))
  }

  test("refer to local variable") {
    val (circuit, global) = untilThisPhase(Vector("test"), "Top", "UseLocalVariable.tchdl")
    val top = circuit.modules.find(_.name == "Top").get.asInstanceOf[fir.Module]

    val topStmts = top.body.asInstanceOf[fir.Block].stmts
    val whens = topStmts.collect{ case c: fir.Conditionally => c }
    assert(whens.length == 1)
    val when = whens.head
    val funcStmts = when.conseq.asInstanceOf[fir.Block].stmts
    assert(funcStmts.length == 3)
    val wires = funcStmts.collect{ case wire: fir.DefWire => wire }
    assert(wires.length == 1)
    val wire = wires.head

    val funcCode = extractHashCode("func_([0-9a-f]+)\\$0\\$local_0", wire.name)
    val localName = concatNames("func", funcCode, "0", "local_0")
    val inName = concatNames("func", funcCode, "in")
    val retName = concatNames("func", funcCode, "_ret")

    val bit8 = fir.UIntType(fir.IntWidth(8))
    assert(funcStmts(0) == fir.DefWire(fir.NoInfo, localName, bit8))
    assert(funcStmts(1) == fir.Connect(fir.NoInfo, fir.Reference(localName, bit8), fir.Reference(inName, bit8)))
    assert(funcStmts(2) == fir.Connect(fir.NoInfo, fir.Reference(retName, bit8), fir.Reference(localName, bit8)))
  }

  test("compile ALU without always statement") {
    val (circuit, global) = untilThisPhase(Vector("test", "alu"), "Top", "ALUwithoutAlways.tchdl")
    val top = circuit.modules.find(_.name == "Top").get.asInstanceOf[fir.Module]
    val aluMod = circuit.modules.find(_.name == "Top_alu").get.asInstanceOf[fir.Module]

    val topStmts = top.body.asInstanceOf[fir.Block].stmts
    val add = topStmts.collectFirst{ case w @ fir.Conditionally(_, fir.Reference(name, _), _, _) if name.contains("add") => w }.get
    val addHash = extractHashCode("add_([0-9a-f]+)\\$_active", add.pred.asInstanceOf[fir.Reference].name)
    val alu = topStmts.collectFirst{ case i: fir.DefInstance => i }.get
    val aluStmts = aluMod.body.asInstanceOf[fir.Block].stmts
    val aluAdd = aluStmts.collectFirst{ case w @ fir.Conditionally(_, fir.Reference(name, _), _, _) if name.contains("add") => w }.get
    val fir.Reference(aluAddName, _) = aluAdd.pred
    val aluHash = extractHashCode("add_([0-9a-f]+)\\$_active", aluAddName)
    val addStmts = add.conseq.asInstanceOf[fir.Block].stmts
    val assigns = addStmts.collect{ case c: fir.Connect => c }

    def genName(name: String): String = s"add_$aluHash$$$name"
    def subRef(name: String, tpe: fir.Type): fir.SubField = fir.SubField(fir.Reference("alu", fir.UnknownType), genName(name), tpe)

    val bit8 = fir.UIntType(fir.IntWidth(8))
    val complex = fir.BundleType(Seq(
      fir.Field("imag", fir.Default, bit8),
      fir.Field("real", fir.Default, bit8)
    ))
    assert(assigns.exists(_.loc == subRef("_active", fir.UIntType(fir.IntWidth(1)))))
    val aAssign = assigns.find(_.loc == subRef("a", complex)).get
    val bAssign = assigns.find(_.loc == subRef("b", complex)).get

    val aSrc = aAssign.expr.asInstanceOf[fir.Reference].name
    val bSrc = bAssign.expr.asInstanceOf[fir.Reference].name

    val aExpr = addStmts.collectFirst{ case fir.DefNode(_, name, expr) if name == aSrc => expr }.get
    val bExpr = addStmts.collectFirst{ case fir.DefNode(_, name, expr) if name == bSrc => expr }.get

    assert(aExpr == fir.Reference(s"add_$addHash$$a", complex))
    assert(bExpr == fir.Reference(s"add_$addHash$$b", complex))
  }

  test("use memory reading and writing") {
    val (circuit, global) = untilThisPhase(Vector("test"), "Top", "useMemory.tchdl")
    val top = circuit.modules.head.asInstanceOf[fir.Module]
    val stmts = top.body.asInstanceOf[fir.Block].stmts
    val reading = stmts.collectFirst{ case w @ fir.Conditionally(_, fir.Reference(name, _), _, _) if name.matches("reading_[0-9a-f]+\\$_active") => w }.get
    val read = stmts.collectFirst{ case w @ fir.Conditionally(_, fir.Reference(name, _), _, _) if name.matches("read_[0-9a-f]+\\$_active") => w }.get
    val mems = stmts.collect{ case m: fir.DefMemory => m }
    assert(mems.length == 1)
    val mem = mems.head

    assert(mem.name == "_mem")
    assert(mem.dataType == fir.UIntType(fir.IntWidth(32)))
    assert(mem.depth == 256)
    assert(mem.readers.length == 2)
    assert(mem.writers.length == 1)
    assert(mem.readLatency == 1)
    assert(mem.writeLatency == 1)

    val regs = stmts.collect{ case r: fir.DefRegister => r }
    assert(regs.length == 2)

    val readingStmts = reading.conseq.asInstanceOf[fir.Block].stmts
    val connects = readingStmts.collect{ case c: fir.Connect => c }

    val connect0 = connects.collectFirst{ case c @ fir.Connect(_, fir.SubIndex(fir.Reference("_mem_0_cycle", _), 0, _), _) => c }.get
    val connect1 = connects.collectFirst{ case c @ fir.Connect(_, fir.SubIndex(fir.Reference("_mem_1_cycle", _), 0, _), _) => c }.get
    assert(connect0.expr == fir.UIntLiteral(1, fir.IntWidth(1)))
    assert(connect1.expr == fir.UIntLiteral(1, fir.IntWidth(1)))

    val readStmts = read.conseq.asInstanceOf[fir.Block].stmts
    val refPointer = readStmts.collectFirst{ case c @ fir.DefNode(_, _, fir.Reference("__pointer_1", _)) => c }.get
    val nodeName = refPointer.name
    val dstRef = readStmts.collectFirst{ case fir.Connect(_, r: fir.Reference, fir.Reference(name, _)) if name == nodeName => r }.get
    assert(dstRef.name.matches("read_[0-9a-f]+\\$_ret"))

    val topConnects = stmts.collect{ case c: fir.Connect => c }
    val pointer1Ref = topConnects.collectFirst{ case fir.Connect(_, fir.SubField(sub: fir.Reference, "_member", _), fir.SubIndex(fir.Reference(name, _), 0, _)) if name == regs(1).name => sub }.get
    assert(pointer1Ref.name == "__pointer_1")
    val dataRefs = topConnects.collect{ case fir.Connect(_, fir.SubField(sub: fir.Reference, "_data", _), src) => src }
    val memRef = fir.Reference("_mem", fir.UnknownType)
    val port = fir.SubField(memRef, "r1", fir.UnknownType)
    val data = fir.SubField(port, "data", fir.UnknownType)
    assert(dataRefs(1) == data)
  }

  test("using multi cycle read latency memory") {
    val (circuit, global) = untilThisPhase(Vector("test"), "Top", "useMemoryMultLatency.tchdl")
    val top = circuit.modules.head.asInstanceOf[fir.Module]
    val stmts = top.body.asInstanceOf[fir.Block].stmts
    val regs = stmts.collect{ case r: fir.DefRegister => r }
    assert(regs.length == 1)
    val cycleReg = regs.head
    assert(cycleReg.tpe == fir.VectorType(fir.UIntType(fir.IntWidth(1)), 2))

    val reg0Ref = fir.SubIndex(fir.Reference("memory_0_cycle", fir.UnknownType), 0, fir.UnknownType)
    val reg1Ref = fir.SubIndex(fir.Reference("memory_0_cycle", fir.UnknownType), 1, fir.UnknownType)

    val connectReg0 = stmts.collectFirst{ case fir.Connect(_, ref, src) if ref == reg0Ref => src }.get
    val connectReg1 = stmts.collectFirst{ case fir.Connect(_, ref, src) if ref == reg1Ref => src }.get
    val connectPointer = stmts.collectFirst{ case fir.Connect(_, ref, src) if src == reg1Ref => ref }.get

    assert(connectReg0 == fir.UIntLiteral(0, fir.IntWidth(1)))
    assert(connectReg1 == reg0Ref)
    assert(connectPointer == fir.SubField(fir.Reference("__pointer_0", fir.UnknownType), "_member", fir.UnknownType))

    val read = stmts.collectFirst{ case w: fir.Conditionally => w }.get
    assert(read.pred.asInstanceOf[fir.Reference].name.matches("read_[0-9a-f]+\\$_active"))
    val readStmts = read.conseq.asInstanceOf[fir.Block].stmts
    val readNodes = readStmts.collect{ case node: fir.DefNode => node }
    assert(readNodes.exists(_.value == fir.Reference("__pointer_0", fir.UnknownType)))
  }
}
