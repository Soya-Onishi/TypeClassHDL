package tchdl

import tchdl.ast._
import tchdl.backend._
import tchdl.util._
import tchdl.typecheck._
import tchdl.backend.ast.{BackendLIR => lir}
import tchdl.parser.Filename

import scala.language.postfixOps
import scala.reflect.ClassTag
import scala.reflect.runtime.universe.TypeTag

class BackendLIRGenTest extends TchdlFunSuite {
  def concatNames(function: String, code: String, remains: String*): String = {
    if(remains.isEmpty) NameTemplate.concat(function, code)
    else NameTemplate.concat(function, code, remains.mkString(NameTemplate.concatCh))
  }

  def parse(filename: String): CompilationUnit =
    parseFile(_.compilation_unit)((gen, tree) => gen(tree, filename))(filename).asInstanceOf[CompilationUnit]

  def untilThisPhase(pkgName: Vector[String], module: String, names: String*): (Vector[lir.Module], GlobalData) = {
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

    val lirModule = BackendLIRGen.exec(moduleContainers, methodContainers)

    (lirModule, newGlobal)
  }

  test("build most simple code") {
    val (modules, _) = untilThisPhase(Vector("test"), "Top[8]", "OnlyTopThrowWire.tchdl")

    val top = modules.find {
      mod =>
        val sameName = mod.tpe.symbol.name == "Top"
        val sameHarg = mod.tpe.hargs.head == HPElem.Num(8)

        sameName && sameHarg
    }.get

    assert(top.ports.length == 3)
    assert(top.ports(0).name.matches("function__active"))
    assert(top.ports(1).name.matches("function_in"))
    assert(top.ports(2).name.matches("function__ret"))

    assert(top.ports(0).dir == lir.Dir.Input)
    assert(top.ports(1).dir == lir.Dir.Input)
    assert(top.ports(2).dir == lir.Dir.Output)

    assert(top.inits.length == 1)
    assert(top.inits.head.isInstanceOf[lir.Invalid])

    assert(top.procedures.length == 1)
    assert(top.procedures.head.isInstanceOf[lir.When])

    val when = top.procedures.head.asInstanceOf[lir.When]
    assert(when.cond.isInstanceOf[lir.Reference])
    assert(when.alt.isEmpty)
    val condRef = when.cond.asInstanceOf[lir.Reference]
    assert(condRef.name.matches("function__active"), condRef.name)
    assert(when.conseq.length == 1)
    assert(when.conseq.head.isInstanceOf[lir.Assign])
    val assign = when.conseq.head.asInstanceOf[lir.Assign]
    assert(assign.dst.isInstanceOf[lir.Reference])
    val dst = assign.dst.asInstanceOf[lir.Reference]
    assert(dst.name.matches("function__ret"), dst.name)
    val src = assign.src.asInstanceOf[lir.Reference]
    assert(src.name.matches("function_in"))
  }

  test("input interface with Unit return type") {
    val (modules, _) = untilThisPhase(Vector("test", "inner"), "Top", "InputUnitFunction.tchdl")
    val top = findModule(modules, "Top").get

    assert(top.ports.length == 1)
    assert(top.ports.head.name.matches("f__active"))

    assert(top.inits.isEmpty)
    assert(top.components.isEmpty)
    assert(top.procedures.length == 1)
    val when = top.procedures.head.asInstanceOf[lir.When]
    assert(when.conseq.isEmpty)
    assert(when.alt.isEmpty)
  }

  test("module that has internal interface and call it") {
    val (modules, global) = untilThisPhase(Vector("test"), "Top", "InputCallInternal.tchdl")
    val top = findModule(modules, "Top").get

    assert(top.ports.length == 3)
    assert(top.ports(0).name.matches("inputFunc__active"))
    assert(top.ports(1).name.matches("inputFunc_in"))
    assert(top.ports(2).name.matches("inputFunc__ret"))

    assert(top.components.length == 3)
    val wires = top.components.collect{ case w: lir.Wire => w }
    assert(wires.length == 3)
    assert(wires(0).name.matches("internalFunc__active"))
    assert(wires(1).name.matches("internalFunc_x"))
    assert(wires(2).name.matches("internalFunc__ret"))

    assert(top.inits.length == 5)
    val (invalids, others) = top.inits.collectPartition{ case invalid: lir.Invalid => invalid }
    assert(invalids.length == 3)
    assert(others(0).isInstanceOf[lir.Node])
    assert(others(1).isInstanceOf[lir.Assign])

    assert(top.procedures.length == 2)
    val whens = top.procedures.collect{ case when: lir.When => when }
    val inputFunc = whens.head
    val internalFunc = whens.tail.head

    val lir.Reference(inputFuncPred, _) = inputFunc.cond
    val lir.Reference(internalFuncPred, _) = internalFunc.cond
    assert(inputFuncPred.matches("inputFunc__active"))
    assert(internalFuncPred.matches("internalFunc__active"))

    assert(inputFunc.conseq.length == 5)
    val Vector(paramNode, litNode, activate, assignArg, retConnect) = inputFunc.conseq
    assert(paramNode.isInstanceOf[lir.Node])
    assert(paramNode.asInstanceOf[lir.Node].src.asInstanceOf[lir.Reference].name.matches("inputFunc_in"))
    assert(litNode.asInstanceOf[lir.Node].src.isInstanceOf[lir.Literal])
    val lir.Assign(activeDst: lir.Reference, _) = activate
    val lir.Assign(argDst: lir.Reference, argSrc: lir.Reference) = assignArg
    val lir.Assign(retDst: lir.Reference, retSrc: lir.Reference) = retConnect

    assert(activeDst.name.matches("internalFunc__active"))
    assert(argDst.name.matches("internalFunc_x"))
    assert(argSrc.name == paramNode.asInstanceOf[lir.Node].name)
    assert(retDst.name.matches("inputFunc__ret"))
    assert(retSrc.name.matches("internalFunc__ret"))

    assert(internalFunc.conseq.length == 1)
    val Vector(lir.Assign(dst, src)) = internalFunc.conseq
    val dstRef = dst.asInstanceOf[lir.Reference]
    val srcRef = src.asInstanceOf[lir.Reference]
    assert(dstRef.name.matches("internalFunc__ret"))
    assert(srcRef.name.matches("internalFunc_x"))

    assert(internalFunc.alt.isEmpty)
  }

  test("refer to local variable") {
    val (modules, global) = untilThisPhase(Vector("test"), "Top", "UseLocalVariable.tchdl")
    val top = findModule(modules, "Top").get

    assert(top.procedures.length == 1)
    assert(top.procedures.head.isInstanceOf[lir.When])
    val when = top.procedures.head.asInstanceOf[lir.When]
    assert(when.conseq.length == 3)
    val wires = when.conseq.collect{ case wire: lir.Wire => wire }
    assert(wires.length == 1)
    val wire = wires.head

    val localName = concatNames("func", "0", "local_0")
    val inName = concatNames("func", "in")
    val retName = concatNames("func", NameTemplate.ret)

    val bit8 = toBackendType(Type.bitTpe(8)(global))(global)
    assert(when.conseq(0) == lir.Wire(localName, bit8))
    assert(when.conseq(1) == lir.Assign(lir.Reference(localName, bit8), lir.Reference(inName, bit8)))
    assert(when.conseq(2) == lir.Assign(lir.Reference(retName, bit8), lir.Reference(localName, bit8)))
  }

  test("compile ALU circuit") {
    val (modules, _) = untilThisPhase(Vector("test", "alu"), "Top", "ALU.tchdl")
    val top = findModule(modules, "Top").get

    val wires = top.procedures.collect{ case w: lir.Wire => w }

    assert(wires.exists(_.name == NameTemplate.concat("adding", "0", "a_0")))
    assert(wires.exists(_.name == NameTemplate.concat("adding", "0", "b_0")))
  }

  test("compile sequential circuit") {
    val (modules, _) = untilThisPhase(Vector("test"), "M", "validSequenceCircuit.tchdl")
    val top = findModule(modules, "M").get
    val name = top.components.collectFirst{ case lir.Reg(name, _, _) => name }.get
    val when = top.procedures
      .collect{ case w: lir.When => w }
      .collectFirst{ case w @ lir.When(lir.Reference(name, _), _, _) if name.contains("function") => w }
      .get

    def genName(name: String): String = s"st1_$name"

    val assigns = when.conseq.collect{ case a: lir.PriorityAssign => a }
    val activeAssignOpt = assigns.find(_.dst.asInstanceOf[lir.Reference].name == genName("_active"))
    val aAssignOpt = assigns.find(_.dst.asInstanceOf[lir.Reference].name == genName("a"))
    val bAssignOpt = assigns.find(_.dst.asInstanceOf[lir.Reference].name == genName("b"))
    val stateAssignOpt = assigns.find(_.dst.asInstanceOf[lir.Reference].name == genName("_state"))

    assert(activeAssignOpt.isDefined)
    assert(aAssignOpt.isDefined)
    assert(bAssignOpt.isDefined)
    assert(stateAssignOpt.isDefined)

    // check current state check works correctly
    val st1When = top.procedures.collectFirst{ case w @ lir.When(lir.Reference(name, _), _, _) if name.matches("st1__active") => w }.get
    val st1Stmts = st1When.conseq
    val st1Nodes = st1Stmts.collect{ case n: lir.Node => n }.collect{ case n @ lir.Node(_, lir.Ops(firrtl.PrimOps.Eq, _, _, _), _) => n }
    val st1LitNodes = st1Stmts.collect{ case n: lir.Node => n }.filter(_.src.isInstanceOf[lir.Literal])

    assert(st1Nodes.length == 2, "\n" + st1Nodes.mkString("\n"))
    val states = st1Stmts.collect{ case w: lir.When => w }
    val stateCondNames = states.collect{ case lir.When(lir.Reference(name, _), _, _) => name }
    assert(stateCondNames.length == 2)
    assert(stateCondNames.contains(st1Nodes(0).name))
    assert(stateCondNames.contains(st1Nodes(1).name))
    val arg00 = st1Nodes(0).src.asInstanceOf[lir.Ops].args(0)
    val arg10 = st1Nodes(1).src.asInstanceOf[lir.Ops].args(0)
    assert(arg00.asInstanceOf[lir.Reference].name.matches("st1__state"))
    assert(arg10.asInstanceOf[lir.Reference].name.matches("st1__state"))
    val arg01 = st1Nodes(0).src.asInstanceOf[lir.Ops].args(1).asInstanceOf[lir.Reference]
    val arg11 = st1Nodes(1).src.asInstanceOf[lir.Ops].args(1).asInstanceOf[lir.Reference]
    val state0 = st1LitNodes.collectFirst{ case lir.Node(name, lir.Literal(value, _), _) if name == arg01.name => value }.get
    val state1 = st1LitNodes.collectFirst{ case lir.Node(name, lir.Literal(value, _), _) if name == arg11.name => value }.get
    assert(state0 == 0)
    assert(state1 == 1)
  }

  test("compile ALU without always statement") {
    val (modules, global) = untilThisPhase(Vector("test", "alu"), "Top", "ALUwithoutAlways.tchdl")
    val top = findModule(modules, "Top").get
    val add = top.procedures.collectFirst{ case w @ lir.When(lir.Reference(name, _), _, _) if name.contains("add") => w }.get

    val alu = top.subs.find(_.name == "alu").get
    val aluMod = findModule(modules, "ALU[Complex[Bit[8]]]").get
    val complex = aluMod.tpe.targs.head
    val aluAdd = aluMod.procedures.collectFirst{ case w @ lir.When(lir.Reference(name, _), _, _) if name.contains("add") => w }.get
    val lir.Reference(aluAddName, _) = aluAdd.cond
    val assigns = add.conseq.collect{ case a: lir.Assign => a }

    // check Port definition
    assert(top.ports.length == 8)
    assert(top.ports.exists(_.name.matches("add_a")))
    assert(top.ports.exists(_.name.matches("add_b")))
    assert(top.ports.exists(_.name.matches("sub_a")))
    assert(top.ports.exists(_.name.matches("sub_b")))

    def genName(name: String): String = s"add_$name"
    def subRef(name: String, tpe: BackendType): lir.SubField = lir.SubField(lir.Reference("alu", alu.tpe), genName(name), tpe)
    val activeAssign = assigns.find(_.dst == subRef("_active", BackendType.bitTpe(1)(global))).get
    val aAssign = assigns.find(_.dst == subRef("a", complex)).get
    val bAssign = assigns.find(_.dst == subRef("b", complex)).get

    val aSrc = aAssign.src.asInstanceOf[lir.Reference].name
    val bSrc = bAssign.src.asInstanceOf[lir.Reference].name

    val aExpr = add.conseq.collectFirst{ case lir.Node(name, expr, _) if name == aSrc => expr }.get
    val bExpr = add.conseq.collectFirst{ case lir.Node(name, expr, _) if name == bSrc => expr }.get

    assert(aExpr == lir.Reference(s"add_a", complex))
    assert(bExpr == lir.Reference(s"add_b", complex))
  }

  test("module that calls sibling modules") {
    val (modules, global) = untilThisPhase(Vector("test"), "Top", "useSiblingInterface.tchdl")
    val sub0 = findModule(modules, "Sub0").get
    val sub1 = findModule(modules, "Sub1").get
    val when = sub0.procedures.collectFirst{ case w @ lir.When(lir.Reference(name, _), _, _) if name.contains("callSibling") => w }.get
    val fromSiblingActive = sub1.procedures.collectFirst{ case w @ lir.When(lir.Reference(name, _), _, _) if name.contains("fromSibling") => name }.get

    val assigns = when.conseq.collect{ case a: lir.Assign => a }
    val activeAssign = assigns.head
    assert(activeAssign.dst == lir.Reference(s"s1_fromSibling__active", BackendType.bitTpe(1)(global)))
    val nodeName = activeAssign.src.asInstanceOf[lir.Reference].name
    val node = when.conseq.collectFirst{ case n @ lir.Node(name, _, _) if nodeName == name => n }.get
    assert(node.src == lir.Literal(1, BackendType.bitTpe(1)(global)))
  }

  test("module that call parent modules") {
    val (modules, global) = untilThisPhase(Vector("test"), "Top", "callParentInterface0.tchdl")
    val top = findModule(modules, "Top").get
    val sub = findModule(modules, "Sub").get
    val calledFromSub = top.procedures.collectFirst{ case w @ lir.When(lir.Reference(name, _), _, _) if name.contains("calledFromSub") => w }.get
    val callParent = sub.procedures.collectFirst{ case w @ lir.When(lir.Reference(name, _), _, _) if name.contains("callParent") => w }.get
    val fromSubName = calledFromSub.cond.asInstanceOf[lir.Reference].name

    val active = callParent.conseq.collectFirst{ case lir.Assign(lir.Reference(name, _), _) if name.contains("_active") => name }.get
    assert(active == s"top_calledFromSub__active")
  }

  test("module that is called from two indirect sibling modules") {
    val (modules, global) = untilThisPhase(Vector("test"), "Top", "callSiblingInterface1.tchdl")
    val top = findModule(modules, "Top").get
    val sub0 = findModule(modules, "Sub0").get
    val sub1 = findModule(modules, "Sub1").get
    val sub2 = findModule(modules, "Sub2").get

    val callName = sub0.procedures.collectFirst{ case lir.When(ref @ lir.Reference(name, _), _, _) if name.contains("call") => ref }.get
    val whens = top.procedures.collect{ case w: lir.When => w }
    val sub1Call = whens.collectFirst{ case w @ lir.When(lir.SubField(lir.Reference("sub1", _), _, _), _, _) => w }.get
    val sub2Call = whens.collectFirst{ case w @ lir.When(lir.SubField(lir.Reference("sub2", _), _, _), _, _) => w }.get
    val sub1sub0Assign = sub1Call.conseq.collectFirst{ case a @ lir.Assign(lir.SubField(_, name, _), _) if name.contains("_active") => a }.get
    val sub2sub0Assign = sub2Call.conseq.collectFirst{ case a @ lir.Assign(lir.SubField(_, name, _), _) if name.contains("_active") => a }.get

    assert(sub1sub0Assign.dst == lir.SubField(lir.Reference("sub0", sub0.tpe), s"call__active", BackendType.bitTpe(1)(global)))
    assert(sub2sub0Assign.dst == lir.SubField(lir.Reference("sub0", sub0.tpe), s"call__active", BackendType.bitTpe(1)(global)))
  }

  test("use enum type as interface's parameter type") {
    val (modules, global) = untilThisPhase(Vector("test"), "Top", "enumWithInterfaceParam3.tchdl")
    val top = findModule(modules, "Top").get

    val inputOpt = top.ports.find(_.name.contains("opt")).get
    val outputRet = top.ports.find(_.name.contains("_ret")).get

    assert(inputOpt.tpe.symbol.name == "Option")
    assert(inputOpt.tpe.targs.length == 1)
    assert(inputOpt.tpe.targs.head == toBackendType(Type.bitTpe(8)(global))(global))

    assert(top.procedures.length == 1)
    val when = top.procedures.head.asInstanceOf[lir.When]
    assert(when.conseq.length == 1)
    assert(when.conseq.head.isInstanceOf[lir.Assign])
    val lir.Assign(dst: lir.Reference, src: lir.Reference) = when.conseq.head

    assert(dst.name.matches("f__ret"), dst.name)
    assert(src.name.matches("f_opt"), src.name)
  }

  test("construct hardware simple enum Option[Bit[2]]") {
    val (modules, global) = untilThisPhase(Vector("test"), "Mod", "ConstructEnum0.tchdl")
    val top = findModule(modules, "Mod").get

    val when = top.procedures.collect{ case when: lir.When => when }.head

    val initFieldName = when.conseq.collectFirst{ case node: lir.Node => node }.get
    val wire = when.conseq.collectFirst{ case wire: lir.Wire => wire }.get
    val connects = when.conseq.collect{ case connect: lir.Assign => connect }

    val enum = wire.name
    val opt = wire.tpe

    assert(connects(0).dst == lir.SubField(lir.Reference(enum, opt), "_member", opt.copy(flag = opt.flag | BackendTypeFlag.EnumFlag)))
    assert(connects(1).dst == lir.SubField(lir.Reference(enum, opt), "_data", opt.copy(flag = opt.flag | BackendTypeFlag.EnumData)))

    assert(connects(0).src.isInstanceOf[lir.Reference])
    assert(connects(1).src.isInstanceOf[lir.Reference])
  }

  test("construct software simple enum Option[Int]") {
    val (modules, global) = untilThisPhase(Vector("test"), "Mod", "ConstructEnum1.tchdl")
    val top = findModule(modules, "Mod").get

    assert(top.procedures.length == 1)
    assert(top.procedures.head.isInstanceOf[lir.When])
    val when = top.procedures.head.asInstanceOf[lir.When]

    val elems = when.conseq
    val bit32 = toBackendType(Type.bitTpe(32)(global))(global)

    assert(elems(0) == lir.Node("_GEN_0", lir.Literal(1, bit32), bit32))
    assert(elems(5).isInstanceOf[lir.Invalid])
    assert(elems(7).isInstanceOf[lir.Assign])
    val dstTpe = elems(7).asInstanceOf[lir.Assign].dst.asInstanceOf[lir.SubField].prefix.tpe
    val opt = BackendType(BackendTypeFlag.NoFlag, dstTpe.symbol, dstTpe.hargs, dstTpe.targs)
    val optData = opt.copy(flag = opt.flag | BackendTypeFlag.EnumData)
    assert(opt.symbol.name == "Opt")
    val dst = lir.SubField(lir.Reference("_ENUM_0", opt), "_data", optData)
    val src = lir.Reference("_GEN_2", optData)
    assert(elems(7) == lir.Assign(dst, src))
  }

  test("construct hardware simple enum Option[Bit[2]]] however None") {
    val (modules, global) = untilThisPhase(Vector("test"), "Mod", "ConstructEnum2.tchdl")
    val top = findModule(modules, "Mod").get

    assert(top.procedures.length == 1)
    assert(top.procedures.head.isInstanceOf[lir.When])
    val when = top.procedures.head.asInstanceOf[lir.When]
    val connects = when.conseq.collect{ case c: lir.Assign => c }
    val nodes = when.conseq.collect{ case n: lir.Node => n }

    val bit1 = toBackendType(Type.bitTpe(1)(global))(global)
    val node = nodes.find(_.src == lir.Literal(0, bit1)).get
    val ref = lir.Reference(node.name, bit1)
    val connect = connects.find(_.src == ref).get
    val opt = connect.dst.asInstanceOf[lir.SubField].prefix.tpe

    assert(connect.dst == lir.SubField(lir.Reference("_ENUM_0", opt), "_member", opt.copy(flag = opt.flag | BackendTypeFlag.EnumFlag)))
  }

  test("construct hardware complex enum three patterns") {
    val (modules, _) = untilThisPhase(Vector("test"), "Top", "ConstructEnum3.tchdl")
    val top = findModule(modules, "Top").get

    val whens = top.procedures.collect{ case w: lir.When => w }
    val constructEmpty = whens.find(_.cond.asInstanceOf[lir.Reference].name.contains("constructEmpty")).get
    val constructSimple = whens.find(_.cond.asInstanceOf[lir.Reference].name.contains("constructSimple")).get
    val constructStruct = whens.find(_.cond.asInstanceOf[lir.Reference].name.contains("constructStruct")).get

    val emptyLit = constructEmpty.conseq.collectFirst{ case lir.Node(_, lit: lir.Literal, _) => lit }.get
    val simpleLit = constructSimple.conseq.collectFirst{ case lir.Node(_, lit: lir.Literal, _) => lit }.get
    val structLit = constructStruct.conseq.collectFirst{ case lir.Node(_, lit @ lir.Literal(v, _), _) if v == 2 => lit }.get

    assert(emptyLit.value == 0)
    assert(simpleLit.value == 1)
    assert(structLit.value == 2)
  }

  test("pattern match Option[Bit[2]] but two Some pattern generates firrtl correctly") {
    def findConseq(when: lir.When, cond: String): Option[Vector[lir.Stmt]] = {
      val name = when.cond.asInstanceOf[lir.Reference].name
      if(name == cond) Some(when.conseq)
      else when.alt.collect{ case w: lir.When => w }.map(findConseq(_, cond)).find(_.isDefined).flatten
    }

    val (modules, _) = untilThisPhase(Vector("test"), "Top", "PatternMatch0.tchdl")
    val top = findModule(modules, "Top").get
    val when = top.procedures.collectFirst{ case w: lir.When => w }.get
    val wire = when.conseq.collectFirst{ case w: lir.Wire => w }.get
    val patternCond = when.conseq.collectFirst{ case node @ lir.Node("_GEN_4", _, _) => node }.get

    val innerWhen = when.conseq.collectFirst{ case w: lir.When => w }.get
    val conseqOpt = findConseq(innerWhen, patternCond.name)
    assert(conseqOpt.isDefined)
    val conseq = conseqOpt.get

    val Vector(lir.Assign(dst: lir.Reference, src: lir.Reference)) = conseq
    assert(dst.name == wire.name)
    assert(src.name.contains("bit"))
  }

  test("pattern match Option[Int]") {
    val (modules, _) = untilThisPhase(Vector("test"), "Top", "PatternMatch7.tchdl")
    val top = findModule(modules, "Top").get
    val whens = top.procedures.collect{ case w: lir.When => w }
    val when = whens.find(_.cond.asInstanceOf[lir.Reference].name.matches("function1__active")).get

    val extWireOpt = when.conseq.collectFirst{ case a @ lir.Node("_EXTRACT_2", _, _) => a }
    assert(extWireOpt.isDefined)

    val extNode = when.conseq.collectFirst{ case node @ lir.Node(_, lir.Ops(_, Vector(lir.Reference("_EXTRACT_2", _), _), _, _), _) => node }.get
    val memberNode = when.conseq.collectFirst{ case node @ lir.Node(_, lir.Ops(_, Vector(lir.SubField(_, "_member", _), _), _, _), _) => node }.get

    def equal(ref: lir.Reference*): Boolean = {
      val names = ref.toVector.map(_.name)
      names.contains(extNode.name) && names.contains(memberNode.name)
    }
    val equalOpt = when.conseq.collectFirst{
      case node @ lir.Node(_, lir.Ops(_, Vector(ref0: lir.Reference, ref1: lir.Reference), _, _), _) if equal(ref0, ref1) => node
    }

    assert(equalOpt.isDefined)
  }

  test("call all binary operation of Bit[_]") {
    import firrtl.PrimOps._

    val (modules, _) = untilThisPhase(Vector("test"), "Top", "useAllBinOpBit.tchdl")
    val top = findModule(modules, "Top").get
    val when = top.procedures.collectFirst{ case w: lir.When => w }.get
    val exprs = when.conseq.collect{ case lir.Node(_, ops: lir.Ops, _) => ops }
    val (_, ops) = exprs.collectPartition{ case op @ lir.Ops(Bits, _, _, _) => op }

    assert(ops(0).op == Add)
    assert(ops(1).op == Sub)
    assert(ops(2).op == Mul)
    assert(ops(3).op == Div)
    assert(ops(4).op == Eq)
    assert(ops(5).op == Neq)
    assert(ops(6).op == Lt)
    assert(ops(7).op == Leq)
    assert(ops(8).op == Gt)
    assert(ops(9).op == Geq)
    assert(ops(10).op == Dshr)
    assert(ops(11).op == Dshl)
    assert(ops(12).op == Dshr)
    assert(ops(13).op == Dshl)
    assert(ops(14).op == Dshr)
    assert(ops(15).op == Dshl)
    assert(ops(16).op == Or)
    assert(ops(17).op == And)
    assert(ops(18).op == Xor)
  }

  test("call all binary operation of Int") {
    untilThisPhase(Vector("test"), "Top", "useAllBinOpInt.tchdl")
  }


  test("use state parameter with Bit[8]") {
    val (modules, _) = untilThisPhase(Vector("test"), "Top", "useStateParam1.tchdl")
    val top = findModule(modules, "Top").get

    val nodes = findAllComponents[lir.Node](top.components ++ top.inits ++ top.procedures)
    val wires = findAllComponents[lir.Wire](top.components ++ top.inits ++ top.procedures)
    val regs = findAllComponents[lir.Reg](top.components ++ top.inits ++ top.procedures)

    val execActive = top.components.collectFirst{ case r @ lir.Reg(name, _, _) if name.contains("exec") && name.contains("_active") => r }.get
    def execName(name: String): String = s"exec_$name"

    // node node_name <= source_wire_name
    //      ^^^^^^^^^    ^^^^^^^^^^^^^^^^
    //      return val   argument('name')
    def findSourceNode(name: String): lir.Reference = {
      nodes.collectFirst{
        case lir.Node(dst, lir.Reference(ref, _), tpe) if name == ref => lir.Reference(dst, tpe)
      }.get
    }

    val a = findSourceNode(execName("a"))
    val b = findSourceNode(execName("b"))
    val c = findSourceNode(execName("c"))
    val d = findSourceNode(execName("d"))
    val addNodeOpt0 = nodes.find(_.src == lir.Ops(firrtl.PrimOps.Add, Vector(a, b), Vector.empty, a.tpe))
    val addNodeOpt1 = nodes.find(_.src == lir.Ops(firrtl.PrimOps.Add, Vector(c, d), Vector.empty, c.tpe))

    assert(addNodeOpt0.isDefined)
    assert(addNodeOpt1.isDefined)

    val addNode0 = addNodeOpt0.get
    val addNode1 = addNodeOpt1.get

    val execFirstLocals = wires.collect{
      case w @ lir.Wire(name, _) if name.contains("exec") && name.contains("first") => w
    }
    val execFirstX = execFirstLocals.find(_.name.contains("x")).get
    val execFirstY = execFirstLocals.find(_.name.contains("y")).get

    val assigns = findAllComponents[lir.Assign](top.components ++ top.inits ++ top.procedures)
      .collect{ case a @ lir.Assign(_: lir.Reference, _) => a }

    val xAssign = assigns.find(_.dst.asInstanceOf[lir.Reference].name == execFirstX.name).get
    val yAssign = assigns.find(_.dst.asInstanceOf[lir.Reference].name == execFirstY.name).get

    assert(xAssign.src == lir.Reference(addNode0.name, addNode0.tpe))
    assert(yAssign.src == lir.Reference(addNode1.name, addNode1.tpe))

    val execSecondX = regs.find(r => r.name.contains("exec") && r.name.contains("second") && r.name.contains("x")).get
    val execSecondY = regs.find(r => r.name.contains("exec") && r.name.contains("second") && r.name.contains("y")).get

    val xAssign0 = assigns.find(_.dst.asInstanceOf[lir.Reference].name == execSecondX.name).get
    val yAssign0 = assigns.find(_.dst.asInstanceOf[lir.Reference].name == execSecondY.name).get

    val xAssignNode0 = nodes.find(_.name == xAssign0.src.asInstanceOf[lir.Reference].name).get
    val yAssignNode0 = nodes.find(_.name == yAssign0.src.asInstanceOf[lir.Reference].name).get

    assert(xAssignNode0.src.asInstanceOf[lir.Reference].name  == execFirstX.name)
    assert(yAssignNode0.src.asInstanceOf[lir.Reference].name  == execFirstY.name)
  }

  test("use state parameter for generate and relay") {
    val (modules, _) = untilThisPhase(Vector("test"), "Top", "useStateParam2.tchdl")
    val top = findModule(modules, "Top").get

    def contains(src: String, keywords: String*): Boolean = {
      keywords.forall(word => src.contains(word))
    }

    val regs = findAllComponents[lir.Reg](top.components ++ top.inits ++ top.procedures)
    val nodes = findAllComponents[lir.Node](top.components ++ top.inits ++ top.procedures)
    val assigns = findAllComponents[lir.PriorityAssign](top.components ++ top.inits ++ top.procedures)
      .collect{ case a @ lir.PriorityAssign(_: lir.Reference, _, _) => a }

    val function = top.procedures.collect{ case w @ lir.When(lir.Reference(name, _), _, _) if name.contains("s0") && name.contains("_active") => w }
    val s0st1x = regs.collectFirst{ case r @ lir.Reg(name, _, _) if contains(name, "s0", "st1", "x") => r }.get
    val s0st1y = regs.collectFirst{ case r @ lir.Reg(name, _, _) if contains(name, "s0", "st1", "y") => r }.get
    val assignX = assigns.find(_.dst.asInstanceOf[lir.Reference].name == s0st1x.name).get
    val assignY = assigns.find(_.dst.asInstanceOf[lir.Reference].name == s0st1y.name).get
    val nodeX = nodes.find(_.name == assignX.src.asInstanceOf[lir.Reference].name).get
    val nodeY = nodes.find(_.name == assignY.src.asInstanceOf[lir.Reference].name).get
    val functionV0 = top.ports.find(p => contains(p.name, "function", "v0")).get
    val functionV1 = top.ports.find(p => contains(p.name, "function", "v1")).get

    assert(nodeX.src == lir.Reference(functionV0.name, functionV0.tpe))
    assert(nodeY.src == lir.Reference(functionV1.name, functionV1.tpe))
  }

  test("method call with cast variable") {
    val (modules, global) = untilThisPhase(Vector("test"), "Top", "castToCallMethod.tchdl")
    val top = findModule(modules, "Top").get
    val function = top.procedures.collectFirst{ case w: lir.When => w }.get
    val nodes = findAllComponents[lir.Node](function.conseq)
    val lit32 = nodes.find(_.src == lir.Literal(32, BackendType.intTpe(global)))
    val lit64 = nodes.find(_.src == lir.Literal(64, BackendType.intTpe(global)))

    assert(lit32.isDefined)
    assert(lit64.isEmpty)
  }


  test("static method call with cast Type") {
    val (modules, global) = untilThisPhase(Vector("test"), "Top", "castToSelectMethod.tchdl")
    val top = findModule(modules, "Top").get
    val function = top.procedures.collectFirst{ case w: lir.When => w }.get
    val nodes = findAllComponents[lir.Node](function.conseq)
    val lit32 = nodes.find(_.src == lir.Literal(32, BackendType.intTpe(global)))
    val lit64 = nodes.find(_.src == lir.Literal(64, BackendType.intTpe(global)))

    assert(lit32.isDefined)
    assert(lit64.isEmpty)
  }

  test("call static method from type parameter with cast") {
    val (modules, global) = untilThisPhase(Vector("test"), "Top", "castTPtoCallStatic.tchdl")
    val top = findModule(modules, "Top").get
    val function = top.procedures.collectFirst{ case w: lir.When => w }.get
    val nodes = findAllComponents[lir.Node](function.conseq)
    val lit32 = nodes.find(_.src == lir.Literal(32, BackendType.intTpe(global)))
    val lit64 = nodes.find(_.src == lir.Literal(64, BackendType.intTpe(global)))

    assert(lit32.isDefined)
    assert(lit64.isEmpty)
  }

  test("call normal method from type parameter with cast") {
    val (modules, global) = untilThisPhase(Vector("test"), "Top", "castTPtoCallNormal.tchdl")
    val top = findModule(modules, "Top").get
    val function = top.procedures.collectFirst{ case w: lir.When => w }.get
    val nodes = findAllComponents[lir.Node](function.conseq)
    val lit32 = nodes.find(_.src == lir.Literal(32, BackendType.intTpe(global)))
    val lit64 = nodes.find(_.src == lir.Literal(64, BackendType.intTpe(global)))

    assert(lit32.isDefined)
    assert(lit64.isEmpty)
  }

  test("refer field type in function signature causes no error") {
    // this only verify phases passed correctly
    untilThisPhase(Vector("test"), "Top", "referFieldTypeInSignature3.tchdl")
  }

  test("use bit manipulation methods") {
    val (modules, _) = untilThisPhase(Vector("test"), "Top", "useBitManipulationMethod.tchdl")
    val top = findModule(modules, "Top").get
    val caller = top.procedures.collectFirst{ case w: lir.When => w }.get
    val nodes = findAllComponents[lir.Node](caller.conseq)
    val ops = nodes.collect{ case lir.Node(_, ops: lir.Ops, _) => ops }

    assert(ops.length == 4)
    assert(ops(0).consts == Seq(7, 3))
    assert(ops(0).op == firrtl.PrimOps.Bits)
    assert(ops(1).consts == Seq(2, 1))
    assert(ops(1).op == firrtl.PrimOps.Bits)
    assert(ops(2).consts == Seq(4, 4))
    assert(ops(2).op == firrtl.PrimOps.Bits)
    assert(ops(3).op == firrtl.PrimOps.Cat)
  }

  test("read registers by static and dynamic index") {
    def contains(src: String, keywords: String*): Boolean = {
      keywords.forall(word => src.contains(word))
    }

    val (modules, global) = untilThisPhase(Vector("test"), "Top", "useVector.tchdl")
    val top = findModule(modules, "Top").get
    val readDyn = top.procedures.collectFirst{ case w @ lir.When(lir.Reference(cond, _), _, _) if cond.contains("readDyn") => w }.get
    val nodes = findAllComponents[lir.Node](readDyn.conseq)
    val assigns = findAllComponents[lir.Assign](readDyn.conseq)

    val dyn = assigns.find(_.src.isInstanceOf[lir.SubAccess]).get
    val subAccess = dyn.src.asInstanceOf[lir.SubAccess]
    val idxRef = nodes.collectFirst{ case n @ lir.Node(_, lir.Reference(name, _), _) if contains(name, "readDyn", "idx") => n }.get
    val vecRef = nodes.collectFirst{ case n @ lir.Node(_, lir.Reference("regs", _), _) => n }.get

    assert(subAccess.idx == lir.Reference(idxRef.name, idxRef.tpe))
    assert(subAccess.vec == lir.Reference(vecRef.name, vecRef.tpe))
  }

  test("write registers by assignment") {
    def contains(src: String, keywords: String*): Boolean = {
      keywords.forall(word => src.contains(word))
    }

    val (modules, global) = untilThisPhase(Vector("test"), "Top", "useAssign.tchdl")
    val top = findModule(modules, "Top").get
    val nodes = findAllComponents[lir.Node](top.components ++ top.inits ++ top.procedures)

    def test(funcName: String, regName: String)(checker: lir.Assign => Unit): Unit = {
      val f = top.procedures.collectFirst{ case w @ lir.When(lir.Reference(name, _), _, _) if contains(name, funcName, "_active") => w }.get
      val assigns = findAllComponents[lir.Assign](f.conseq)
      val assign = assigns.collectFirst{ case a @ lir.Assign(lir.Reference(name, _), _) if name == regName => a }.get

      checker(assign)
    }

    test("function0", "a"){ assign =>
      val nodeName = assign.src.asInstanceOf[lir.Reference].name
      val node = nodes.find(_.name == nodeName).get
      assert(node.src == lir.Literal(0, BackendType.bitTpe(2)(global)))
    }

    test("function1", "vec") { assign =>
      assert(assign.src.isInstanceOf[lir.Reference])
      val refName = assign.src.asInstanceOf[lir.Reference].name
      assert(refName.matches("function1_vec"))
    }

  }

  test("use vector update") {
    val (modules, global) = untilThisPhase(Vector("test"), "Top", "useVectorUpdate.tchdl")
    val top = findModule(modules, "Top").get
    val updateReg = top.procedures.collectFirst{ case w @ lir.When(ref: lir.Reference, _, _) if ref.name.matches("updateReg__active") => w }.get
    val updateFirstReg = top.procedures.collectFirst{ case w @ lir.When(ref: lir.Reference, _, _) if ref.name.matches("updateFirstReg__active") => w }.get

    {
      val nodes = findAllComponents[lir.Node](updateReg.conseq)
      val assigns = findAllComponents[lir.Assign](updateReg.conseq)
      val refRegs = nodes.find(_.src.asInstanceOf[lir.Reference].name == "regs").get
      val refIdx = nodes.find(_.src.asInstanceOf[lir.Reference].name.matches("updateReg_idx")).get
      val refElem = nodes.find(_.src.asInstanceOf[lir.Reference].name.matches("updateReg_elem")).get

      val assignUpdate = assigns.collectFirst { case a @ lir.Assign(lir.Reference("_VEC_UPDATED_0", _), _) => a }.get
      val assignAccess = assigns.find(_.dst.isInstanceOf[lir.SubAccess]).get
      val assignRegs = assigns.collectFirst{ case a @ lir.Assign(lir.Reference("regs", _), _) => a }.get

      assert(assignUpdate.src == lir.Reference(refRegs.name, refRegs.tpe))
      assert(assignAccess.src == lir.Reference(refElem.name, refElem.tpe))
      assert(assignAccess.dst.asInstanceOf[lir.SubAccess].idx == lir.Reference(refIdx.name, refIdx.tpe))
      assert(assignRegs.src == lir.Reference("_VEC_UPDATED_0", assignRegs.src.tpe))
    }
  }

  test("pattern match with bool type") {
    val (modules, global) = untilThisPhase(Vector("test"), "Top", "PatternMatch9.tchdl")
    val top = findModule(modules, "Top").get
    val f = top.procedures.collectFirst{ case w: lir.When => w }.get

    val bit1 = BackendType.boolTpe(global)
    val bool = BackendType(BackendTypeFlag.NoFlag, Symbol.bool(global), Vector.empty, Vector.empty)
    val nodes = findAllComponents[lir.Node](f.conseq)
    val aNode = nodes.collectFirst{ case n @ lir.Node(_, lir.Reference(name, _), _) if name.matches("f_a") => n }.get
    val lit1Node = nodes.collectFirst{ case n @ lir.Node(_, lir.Literal(v, _), _) if v == 1 => n }.get
    val lit0Node = nodes.collectFirst{ case n @ lir.Node(_, lir.Literal(v, _), _) if v == 0 => n }.get
    val eqNodes = nodes.collect{ case n @ lir.Node(_, _: lir.Ops, _) => n }
    val eqs = eqNodes.map(_.src.asInstanceOf[lir.Ops])
    assert(eqs(0).args == Vector(lir.Reference(aNode.name, bool), lir.Reference(lit1Node.name, bit1)))
    assert(eqs(1).args == Vector(lir.Reference(aNode.name, bool), lir.Reference(lit0Node.name, bit1)))

    val when0 = f.conseq.collectFirst{ case w: lir.When => w }.get
    assert(when0.cond == lir.Reference(eqNodes(0).name, bit1))
    val when1 = when0.alt.collectFirst{ case w: lir.When => w }.get
    assert(when1.cond == lir.Reference(eqNodes(1).name, bit1))
  }

  test("pattern match with Int type") {
    val (modules, global) = untilThisPhase(Vector("test"), "Top", "PatternMatch10.tchdl")
    val top = findModule(modules, "Top").get
    val f = top.procedures.collectFirst { case w: lir.When => w }.get

    val int = BackendType.intTpe(global)
    val bool = BackendType.boolTpe(global)
    val nodes = f.conseq.collect{ case n: lir.Node => n }
    val aNode = nodes.collectFirst{ case n @ lir.Node(_, lir.Reference(name, _), _) if name.matches("f_a") => n }.get
    val litNodes = nodes.collect{ case n @ lir.Node(_, _: lir.Literal, _) => n }
    val eqNodes = nodes.collect{ case n @ lir.Node(_, _: lir.Ops, _) => n }

    assert(litNodes.length == 3)
    assert(litNodes(0).src == lir.Literal(0, int))
    assert(litNodes(1).src == lir.Literal(1, int))
    assert(litNodes(2).src == lir.Literal(1, bool))

    val a = lir.Reference(aNode.name, aNode.tpe)
    val lit0 = lir.Reference(litNodes(0).name, litNodes(0).tpe)
    val lit1 = lir.Reference(litNodes(1).name, litNodes(1).tpe)
    assert(eqNodes(0).src == lir.Ops(firrtl.PrimOps.Eq, Vector(a, lit0), Vector.empty, bool))
    assert(eqNodes(1).src == lir.Ops(firrtl.PrimOps.Eq, Vector(a, lit1), Vector.empty, bool))

    val when0 = f.conseq.collectFirst{ case w: lir.When => w }.get
    assert(when0.cond == lir.Reference(eqNodes(0).name, bool))
    val when1 = when0.alt.collectFirst{ case w: lir.When => w }.get
    assert(when1.cond == lir.Reference(eqNodes(1).name, bool))
    val when2 = when1.alt.collectFirst{ case w: lir.When => w }.get
    assert(when2.cond == lir.Reference(litNodes(2).name, bool))
  }

  test("pattern match with Bit[2] type") {
    val (modules, global) = untilThisPhase(Vector("test"), "Top", "PatternMatch11.tchdl")
    val top = findModule(modules, "Top").get
    val f = top.procedures.collectFirst { case w: lir.When => w }.get

    val bit = BackendType.bitTpe(2)(global)
    val bool = BackendType.boolTpe(global)
    val nodes = f.conseq.collect{ case n: lir.Node => n }
    val aNode = nodes.collectFirst{ case n @ lir.Node(_, lir.Reference(name, _), _) if name.matches("f_a") => n }.get
    val litNodes = nodes.collect{ case n @ lir.Node(_, _: lir.Literal, _) => n }
    val eqNodes = nodes.collect{ case n @ lir.Node(_, _: lir.Ops, _) => n }

    assert(litNodes.length == 3)
    assert(litNodes(0).src == lir.Literal(0, bit))
    assert(litNodes(1).src == lir.Literal(1, bit))
    assert(litNodes(2).src == lir.Literal(1, bool))

    val a = lir.Reference(aNode.name, aNode.tpe)
    val lit0 = lir.Reference(litNodes(0).name, litNodes(0).tpe)
    val lit1 = lir.Reference(litNodes(1).name, litNodes(1).tpe)
    assert(eqNodes(0).src == lir.Ops(firrtl.PrimOps.Eq, Vector(a, lit0), Vector.empty, bool))
    assert(eqNodes(1).src == lir.Ops(firrtl.PrimOps.Eq, Vector(a, lit1), Vector.empty, bool))

    val when0 = f.conseq.collectFirst{ case w: lir.When => w }.get
    assert(when0.cond == lir.Reference(eqNodes(0).name, bool))
    val when1 = when0.alt.collectFirst{ case w: lir.When => w }.get
    assert(when1.cond == lir.Reference(eqNodes(1).name, bool))
    val when2 = when1.alt.collectFirst{ case w: lir.When => w }.get
    assert(when2.cond == lir.Reference(litNodes(2).name, bool))
  }

  test("pattern match with Bit[2] type with ident catcher") {
    val (modules, global) = untilThisPhase(Vector("test"), "Top", "PatternMatch12.tchdl")
    val top = findModule(modules, "Top").get
    val f = top.procedures.collectFirst{ case w: lir.When => w }.get

    val bool = BackendType.boolTpe(global)
    val nodes = f.conseq.collect{ case n: lir.Node => n }
    val litNodes = nodes.collect{ case n @ lir.Node(_, _: lir.Literal, _) => n }
    val eqNode = nodes.collectFirst{ case n @ lir.Node(_, _: lir.Ops, _) => n }.get

    val when0 = f.conseq.collectFirst{ case w: lir.When => w }.get
    assert(when0.cond == lir.Reference(eqNode.name, bool))
    val when1 = when0.alt.collectFirst{ case w: lir.When => w }.get
    assert(when1.cond == lir.Reference(litNodes(1).name, bool))
  }


  test("use cast method to cast some types into Bit[8]") {
    val (modules, global) = untilThisPhase(Vector("test"), "Top", "useFroms.tchdl")
    val top = findModule(modules, "Top").get
    val f0 = top.procedures.collectFirst{ case w @ lir.When(lir.Reference(name, _), _, _) if name.matches("function0__active") => w }.get
    val f1 = top.procedures.collectFirst{ case w @ lir.When(lir.Reference(name, _), _, _) if name.matches("function1__active") => w }.get
    val f2 = top.procedures.collectFirst{ case w @ lir.When(lir.Reference(name, _), _, _) if name.matches("function2__active") => w }.get
    val bit8 = BackendType.bitTpe(8)(global)

    {
      val opNode = f0.conseq.collectFirst{ case n @ lir.Node(_, _: lir.Ops, _) => n }.get
      val assign = f0.conseq.collectFirst{ case a: lir.Assign => a }.get
      val ops = opNode.src.asInstanceOf[lir.Ops]

      assert(ops.op == firrtl.PrimOps.Pad)
      assert(assign.dst.isInstanceOf[lir.Reference])
      assert(assign.dst.asInstanceOf[lir.Reference].name.matches("function0__ret"))
      assert(assign.src == lir.Reference(opNode.name, bit8))
    }

    {
      val opNode = f1.conseq.collectFirst{ case n @ lir.Node(_, _: lir.Ops, _) => n }.get
      val assign = f1.conseq.collectFirst{ case a: lir.Assign => a }.get
      val ops = opNode.src.asInstanceOf[lir.Ops]

      assert(ops.op == firrtl.PrimOps.Bits)
      assert(assign.dst.isInstanceOf[lir.Reference])
      assert(assign.dst.asInstanceOf[lir.Reference].name.matches("function1__ret"))
      assert(assign.src == lir.Reference(opNode.name, bit8))
    }

    {
      val opNode = f2.conseq.collectFirst{ case n @ lir.Node(_, _: lir.Ops, _) => n }.get
      val assign = f2.conseq.collectFirst{ case a: lir.Assign => a }.get
      val ops = opNode.src.asInstanceOf[lir.Ops]

      assert(ops.op == firrtl.PrimOps.Pad)
      assert(assign.dst.isInstanceOf[lir.Reference])
      assert(assign.dst.asInstanceOf[lir.Reference].name.matches("function2__ret"))
      assert(assign.src == lir.Reference(opNode.name, bit8))
    }
  }

  test("use interface's internal interface") {
    val (modules, global) = untilThisPhase(Vector("test"), "Top", "useInterfaceMethodForModule.tchdl")

    val top = findModule(modules, "Top").get
    val sub = findModule(modules, "Sub").get

    val function = top.procedures.collectFirst{ case w: lir.When => w }.get
    val inc = sub.procedures.collectFirst{ case w: lir.When => w }.get
    assert(inc.cond.asInstanceOf[lir.Reference].name == s"TopInterface__inc__active")

    val addNode = inc.conseq.collectFirst{ case n @ lir.Node(_, lir.Ops(firrtl.PrimOps.Add, _, _, _), _) => n }.get
    val assignInc = inc.conseq.collectFirst{ case a: lir.Assign => a }.get
    assert(assignInc.dst == lir.Reference(s"TopInterface__inc__ret", addNode.tpe))
    assert(assignInc.src == lir.Reference(addNode.name, addNode.tpe))

    val bool = BackendType.boolTpe(global)
    val assignFunc = function.conseq.collectFirst{ case a @ lir.Assign(lir.SubField(_, field, _), _) if field.contains("_active") => a }.get
    assert(assignFunc.dst == lir.SubField(lir.Reference("sub", sub.tpe), s"TopInterface__inc__active", bool))
    assert(assignFunc.src.tpe == bool)
  }

  test("elaborate code that uses builder pattern") {
    // run builder pattern
    untilThisPhase(Vector("test"), "Top", "builderPattern.tchdl")
  }


  test("use some vector manipulation methods") {
    untilThisPhase(Vector("test"), "Top", "useVecManipulation.tchdl")
  }

  test("use proc and deref") {
    val (modules, global) = untilThisPhase(Vector("test"), "UseDeref", "procDeref.tchdl")

    val useDeref = findModule(modules, "UseDeref").get
    val nodes = findAllComponents[lir.Node](useDeref.inits ++ useDeref.procedures)
    val whens = useDeref.procedures.collect{ case w: lir.When => w }
    val exec = whens(0)
    val deref = exec.conseq.collectFirst{ case d: lir.Deref => d }.get
    val node = nodes.collectFirst{ case node if node.name == deref.ref.name => node }.get
    val rets = findAllComponents[lir.Return](useDeref.inits ++ useDeref.procedures)

    assert(node.src.isInstanceOf[lir.Reference])
    val ref = node.src.asInstanceOf[lir.Reference]
    assert(ref.name.matches("exec_0_pointer_[0-9]+"), ref.name)

    val next = whens(2)
    val ret = next.conseq.collectFirst{ case r: lir.Return => r }.get
    val srcName = ret.expr.asInstanceOf[lir.Reference].name
    assert(ret.path.name.get == "multCycle")
    assert(srcName.matches("multCycle_next_result"), srcName)

    assert(rets.length == 2)
    assert(rets(1) eq ret)
    assert(rets(0).path == rets(1).path)
    assert(rets(0).expr.isInstanceOf[lir.Reference])
    val retRef = rets(0).expr.asInstanceOf[lir.Reference]
    val defaultNode = nodes.find(_.name == retRef.name).get

    assert(defaultNode.src == lir.Literal(0, BackendType.bitTpe(8)(global)))
  }

  test("read and write memory") {
    val (modules, global) = untilThisPhase(Vector("test"), "Top", "useMemory.tchdl")
    val top = modules.head
    assert(top.mems.length == 1)

    val reading = top.procedures.collectFirst{ case w @ lir.When(lir.Reference(name, _), _, _) if name.matches("reading__active") => w }.get
    val writing = top.procedures.collectFirst{ case w @ lir.When(lir.Reference(name, _), _, _) if name.matches("writing__active") => w }.get
    val memReads = reading.conseq.collect{ case m: lir.MemRead => m }
    val memWrites = writing.conseq.collect{ case m: lir.MemWrite => m }

    assert(memReads.length == 2)
    assert(memWrites.length == 1)

    val memRead0 = memReads(0)
    val memRead1 = memReads(1)
    val memWrite = memWrites.head

    assert(memRead0.port == 0)
    assert(memRead1.port == 1)
    assert(memWrite.port == 0)

    assert(memRead0.name == "_mem")
    assert(memRead1.name == "_mem")
    assert(memWrite.name == "_mem")

    assert(memRead0.tpe.symbol.name == "Option")
    val bit32 = BackendType.bitTpe(32)(global)
    val option = BackendType(BackendTypeFlag.Pointer, memRead0.tpe.symbol, Vector.empty, Vector(bit32))
    assert(memRead0.tpe == option)
    assert(memRead1.tpe == option)

    val rNodes = reading.conseq.collect{ case n: lir.Node => n }
    val wNodes = writing.conseq.collect{ case n: lir.Node => n }

    assert(memRead0.addr.isInstanceOf[lir.Reference])
    val addrNode0 = rNodes.find(_.name == memRead0.addr.asInstanceOf[lir.Reference].name).get
    assert(addrNode0.src.asInstanceOf[lir.Reference].name.matches("reading_addr"))
    assert(memWrite.addr.isInstanceOf[lir.Reference])
    val addrNode1 = wNodes.find(_.name == memWrite.addr.asInstanceOf[lir.Reference].name).get
    assert(addrNode1.src.asInstanceOf[lir.Reference].name.matches("writing_addr"))
  }

  test("if expr multiple same name local variable") {
    val (modules, global) = untilThisPhase(Vector("test"), "Top", "ifexprMultLocalVar.tchdl")
    val top = modules.head
    val function = top.procedures.collectFirst{ case w: lir.When => w }.get
    val fStmts = function.conseq
    val wires = findAllComponents[lir.Wire](fStmts)

    val values = wires.filter(_.name.contains("function"))
    assert(values.forall(_.name.matches("function_(\\d_)+value_0")))
  }

  test("run simple module but use same names at parameter and ident pattern in pattern matching") {
    val (modules, global) = untilThisPhase(Vector("test"), "Top", "useSameName.tchdl")
    val top = modules.head
    val execute = top.procedures.collectFirst{ case w: lir.When => w }.get
    val nodes = findAllComponents[lir.Node](execute.conseq)

    val overlaps = nodes.map(_.name).groupBy(identity).values.toVector.filter(_.length != 1)
    assert(overlaps.isEmpty, s"${overlaps.length} overlaps. [${overlaps.map(_.head).mkString(",")}]")
  }

  test("pattern matching with Enum that has Enum field") {
    val (modules, global) = untilThisPhase(Vector("test"), "Top", "patternMatchEnumInEnum.tchdl")
    val top = modules.head
    val execute = top.procedures.collectFirst{ case w: lir.When => w }.get
    val nodes = findAllComponents[lir.Node](execute.conseq)
    val extracts = nodes.collect{ case lir.Node(_, e: lir.Extract, _) => e }
    val first = extracts.head
    val second = extracts.tail.head

    assert(first.history.length == 1)
    assert(first.history.head.flag.hasFlag(BackendTypeFlag.EnumData))
    assert(second.history.length == 2)
    assert(second.history.head.flag.hasFlag(BackendTypeFlag.EnumFlag))
  }

  test("use an output and an input port works correctly") {
    val (modules, global) = untilThisPhase(Vector("test"), "Top", "usePorts.tchdl")
    val top = modules.head
    val assigns = top.procedures.collect{ case a: lir.Assign => a }
    val invalids = top.inits.collect{ case i @ lir.Invalid(_: lir.SubField) => i }

    assert(assigns.length == 2)
    val dsts = assigns.map(_.dst).collect{ case lir.SubField(_, name, _) => name }
    assert(dsts.length == 1)
    assert(dsts.contains("in"))
    val srcs = assigns.map(_.src).collect{ case lir.SubField(_, name, _) => name }
    assert(srcs.length == 1)
    assert(srcs.contains("out"))

    assert(invalids.length == 1)
    assert(invalids.head.name.isInstanceOf[lir.SubField])

    val sub = modules.find(_.tpe.symbol.toString == "Sub").get
    assert(sub.ports.length == 2)
    assert(sub.ports.exists(p => p.dir == lir.Dir.Input && p.name == "in"))
    assert(sub.ports.exists(p => p.dir == lir.Dir.Output && p.name == "out"))
  }

  test("define input and output ports that have default value") {
    val (modules, global) = untilThisPhase(Vector("test"), "Top", "portWithDefault.tchdl")
    val top = modules.head
    val assigns = top.procedures
      .collectFirst{ case w: lir.When => w }.get
      .conseq
      .collect{ case a: lir.Assign => a }

    assert(assigns.length == 3)
    val dsts = assigns.map(_.dst).collect{ case s: lir.SubField => s }
    assert(dsts.length == 2)
    assert(dsts.exists(_.name == NameTemplate.portActive))
    assert(dsts.exists(_.name == NameTemplate.portBits))
    assert(dsts.forall(_.prefix.asInstanceOf[lir.SubField].name == "__in"))

    val sub = modules.tail.head
    val inits = sub.inits
    val wires = inits.collect{ case w: lir.Wire => w }
    val whens = inits.collect{ case w: lir.When => w}
    val outer = whens.head.conseq.head.asInstanceOf[lir.Assign].src.asInstanceOf[lir.SubField]
    val inputs = sub.ports.filter(_.dir == lir.Dir.Input)

    assert(wires.length == 1)
    assert(wires.exists(_.name == "in"))
    assert(whens.length == 1)
    assert(outer.name == NameTemplate.portBits)
    assert(inputs.length == 1)
    assert(inputs.head.tpe.flag.hasFlag(BackendTypeFlag.DefaultInput))
  }
}
