package tchdl

import tchdl.ast._
import tchdl.backend._
import tchdl.util._
import tchdl.typecheck._
import tchdl.backend.ast.{BackendLIR => lir}
import java.nio.file.Files

import tchdl.parser.Filename

import sys.process._
import scala.language.postfixOps
import org.scalatest.tags.Slow

@Slow
class BackendLIRGenTest extends TchdlFunSuite {
  def extractHashCode(regex: String, from: String): String = {
    val r = regex.r
    r.findAllIn(from).matchData.map{ _.group(1) }.toVector.head
  }

  def concatNames(function: String, code: String, remains: String*): String = {
    function + "_" + code + "$" + remains.mkString("$")
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

  /*
  def runFirrtl(circuit: ir.Circuit, print: Boolean = false): Unit = {
    val firrtlFile = Files.createTempFile(null, ".fir")
    val verilogFile = Files.createTempFile(null, ".v")
    Files.write(firrtlFile, circuit.serialize.getBytes)
    val circuitString = Files.readString(firrtlFile)

    val commandArray = Array(
      "/home/soya/opt/firrtl/utils/bin/firrtl",
      "-i",
      firrtlFile.toString,
      "-o",
      verilogFile.toString,
    )

    val command = commandArray.mkString(" ")
    val exit = command !

    if(exit != 0 || print)
      println(circuitString)

    if(exit != 0)
      fail()
  }
  */

  def findModule(modules: Vector[lir.Module], tpeStr: String): Option[lir.Module] = {
    def isSameTpe(tpe: BackendType, tpeTree: TypeTree): Boolean = {
      def toHPElem(harg: HPExpr): HPElem = harg match {
        case IntLiteral(value) => HPElem.Num(value)
        case StringLiteral(str) => HPElem.Str(str)
        case _ => ???
      }

      val TypeTree(Ident(tpeName), hps, tps, _) = tpeTree

      def isSameName = tpe.symbol.name == tpeName
      def isSameHPLen = tpe.hargs.length == hps.length
      def isSameHPElem = tpe.hargs == hps.map(toHPElem)
      def isSameTPLen = tpe.targs.length == tps.length
      def isSameTPElem = (tpe.targs zip tps).forall{ case (t0, t1) => isSameTpe(t0, t1) }

      isSameName && isSameHPLen && isSameTPLen && isSameHPElem && isSameTPElem
    }

    val parser = parseString(_.`type`)((gen, tree) => gen.typeTree(tree)(Filename("")))_
    val tpeTree = parser(tpeStr).asInstanceOf[TypeTree]

    modules.find(mod => isSameTpe(mod.tpe, tpeTree))
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
    assert(top.ports(0).name.matches("function_[0-9a-f]+\\$_active"))
    assert(top.ports(1).name.matches("function_[0-9a-f]+\\$in"))
    assert(top.ports(2).name.matches("function_[0-9a-f]+\\$_ret"))

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
    assert(condRef.name.matches("function_[0-9a-f]+\\$_active"), condRef.name)
    assert(when.conseq.length == 1)
    assert(when.conseq.head.isInstanceOf[lir.Assign])
    val assign = when.conseq.head.asInstanceOf[lir.Assign]
    assert(assign.dst.isInstanceOf[lir.Reference])
    val dst = assign.dst.asInstanceOf[lir.Reference]
    assert(dst.name.matches("function_[0-9a-f]+\\$_ret"), dst.name)
    val src = assign.src.asInstanceOf[lir.Reference]
    assert(src.name.matches("function_[0-9a-f]+\\$in"))
  }

  test("input interface with Unit return type") {
    val (modules, _) = untilThisPhase(Vector("test", "inner"), "Top", "InputUnitFunction.tchdl")
    val top = findModule(modules, "Top").get

    assert(top.ports.length == 1)
    assert(top.ports.head.name.matches("f_[0-9a-f]+\\$_active"))

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
    assert(top.ports(0).name.matches("inputFunc_[0-9a-f]+\\$_active"))
    assert(top.ports(1).name.matches("inputFunc_[0-9a-f]+\\$in"))
    assert(top.ports(2).name.matches("inputFunc_[0-9a-f]+\\$_ret"))

    assert(top.components.length == 3)
    val wires = top.components.collect{ case w: lir.Wire => w }
    assert(wires.length == 3)
    assert(wires(0).name.matches("internalFunc_[0-9a-f]+\\$_active"))
    assert(wires(1).name.matches("internalFunc_[0-9a-f]+\\$x"))
    assert(wires(2).name.matches("internalFunc_[0-9a-f]+\\$_ret"))

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
    assert(inputFuncPred.matches("inputFunc_[0-9a-f]+\\$_active"))
    assert(internalFuncPred.matches("internalFunc_[0-9a-f]+\\$_active"))

    val internalFuncPattern = "internalFunc_([0-9a-f]+)\\$\\w+".r
    val internalFuncCode = internalFuncPattern.findAllIn(internalFuncPred).matchData.map{ _.group(1) }.toVector.head

    assert(inputFunc.conseq.length == 5)
    val Vector(paramNode, litNode, activate, assignArg, retConnect) = inputFunc.conseq
    assert(paramNode.isInstanceOf[lir.Node])
    assert(paramNode.asInstanceOf[lir.Node].src.asInstanceOf[lir.Reference].name.matches("inputFunc_[0-9a-f]+\\$in"))
    assert(litNode.asInstanceOf[lir.Node].src.isInstanceOf[lir.Literal])
    val lir.Assign(activeDst: lir.Reference, _) = activate
    val lir.Assign(argDst: lir.Reference, argSrc: lir.Reference) = assignArg
    val lir.Assign(retDst: lir.Reference, retSrc: lir.Reference) = retConnect

    assert(activeDst.name.matches("internalFunc_[0-9a-f]+\\$_active"))
    assert(argDst.name.matches("internalFunc_[0-9a-f]+\\$x"))
    assert(argSrc.name == paramNode.asInstanceOf[lir.Node].name)
    assert(retDst.name.matches("inputFunc_[0-9a-f]+\\$_ret"))
    assert(retSrc.name.matches("internalFunc_[0-9a-f]+\\$_ret"))

    assert(internalFunc.conseq.length == 1)
    val Vector(lir.Assign(dst, src)) = internalFunc.conseq
    val dstRef = dst.asInstanceOf[lir.Reference]
    val srcRef = src.asInstanceOf[lir.Reference]
    assert(dstRef.name.matches("internalFunc_[0-9a-f]+\\$_ret"))
    assert(srcRef.name.matches("internalFunc_[0-9a-f]+\\$x"))

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

    val funcCode = extractHashCode("func_([0-9a-f]+)\\$0\\$local_0", wire.name)
    val localName = concatNames("func", funcCode, "0", "local_0")
    val inName = concatNames("func", funcCode, "in")
    val retName = concatNames("func", funcCode, "_ret")

    val bit8 = toBackendType(Type.bitTpe(8)(global))(global)
    assert(when.conseq(0) == lir.Wire(localName, bit8))
    assert(when.conseq(1) == lir.Assign(lir.Reference(localName, bit8), lir.Reference(inName, bit8)))
    assert(when.conseq(2) == lir.Assign(lir.Reference(retName, bit8), lir.Reference(localName, bit8)))
  }

  test("compile ALU circuit") {
    val (modules, _) = untilThisPhase(Vector("test", "alu"), "Top", "ALU.tchdl")
    val top = findModule(modules, "Top").get

    val wires = top.procedures.collect{ case w: lir.Wire => w }
    wires.find(_.name == "adding$0$a_0").get
    wires.find(_.name == "adding$0$b_0").get
  }

  test("compile sequential circuit") {
    val (modules, _) = untilThisPhase(Vector("test"), "M", "validSequenceCircuit.tchdl")
    val top = findModule(modules, "M").get
    val name = top.components.collectFirst{ case lir.Reg(name, _, _) => name }.get
    val hash = extractHashCode("st1_([0-9a-f]+)\\$[_a-zA-Z0-9]+", name)
    val when = top.procedures
      .collect{ case w: lir.When => w }
      .collectFirst{ case w @ lir.When(lir.Reference(name, _), _, _) if name.contains("function") => w }
      .get

    def genName(name: String): String = s"st1_$hash$$$name"

    val assigns = when.conseq.collect{ case a: lir.Assign => a }
    val activeAssignOpt = assigns.find(_.dst.asInstanceOf[lir.Reference].name == genName("_active"))
    val aAssignOpt = assigns.find(_.dst.asInstanceOf[lir.Reference].name == genName("a"))
    val bAssignOpt = assigns.find(_.dst.asInstanceOf[lir.Reference].name == genName("b"))
    val stateAssignOpt = assigns.find(_.dst.asInstanceOf[lir.Reference].name == genName("_state"))

    assert(activeAssignOpt.isDefined)
    assert(aAssignOpt.isDefined)
    assert(bAssignOpt.isDefined)
    assert(stateAssignOpt.isDefined)
  }

  test("compile ALU without always statement") {
    val (modules, global) = untilThisPhase(Vector("test", "alu"), "Top", "ALUwithoutAlways.tchdl")
    val top = findModule(modules, "Top").get
    val add = top.procedures.collectFirst{ case w @ lir.When(lir.Reference(name, _), _, _) if name.contains("add") => w }.get
    val addHash = extractHashCode("add_([0-9a-f]+)\\$_active", add.cond.asInstanceOf[lir.Reference].name)
    val alu = top.subs.find(_.name == "alu").get
    val aluMod = findModule(modules, "ALU[Complex[Bit[8]]]").get
    val complex = aluMod.tpe.targs.head
    val aluAdd = aluMod.procedures.collectFirst{ case w @ lir.When(lir.Reference(name, _), _, _) if name.contains("add") => w }.get
    val lir.Reference(aluAddName, _) = aluAdd.cond
    val aluHash = extractHashCode("add_([0-9a-f]+)\\$_active", aluAddName)
    val assigns = add.conseq.collect{ case a: lir.Assign => a }

    def genName(name: String): String = s"add_$aluHash$$$name"
    def subRef(name: String, tpe: BackendType): lir.SubField = lir.SubField(lir.Reference("alu", alu.tpe), genName(name), tpe)
    val activeAssign = assigns.find(_.dst == subRef("_active", BackendType.bitTpe(1)(global))).get
    val aAssign = assigns.find(_.dst == subRef("a", complex)).get
    val bAssign = assigns.find(_.dst == subRef("b", complex)).get

    val aSrc = aAssign.src.asInstanceOf[lir.Reference].name
    val bSrc = bAssign.src.asInstanceOf[lir.Reference].name

    val aExpr = add.conseq.collectFirst{ case lir.Node(name, expr, _) if name == aSrc => expr }.get
    val bExpr = add.conseq.collectFirst{ case lir.Node(name, expr, _) if name == bSrc => expr }.get

    assert(aExpr == lir.Reference(s"add_$addHash$$a", complex))
    assert(bExpr == lir.Reference(s"add_$addHash$$b", complex))
  }

  test("module that calls sibling modules") {
    val (modules, global) = untilThisPhase(Vector("test"), "Top", "useSiblingInterface.tchdl")
    val sub0 = findModule(modules, "Sub0").get
    val sub1 = findModule(modules, "Sub1").get
    val when = sub0.procedures.collectFirst{ case w @ lir.When(lir.Reference(name, _), _, _) if name.contains("callSibling") => w }.get
    val fromSiblingActive = sub1.procedures.collectFirst{ case w @ lir.When(lir.Reference(name, _), _, _) if name.contains("fromSibling") => name }.get
    val siblingHash = extractHashCode("fromSibling_([0-9a-f]+)\\$_active", fromSiblingActive)

    val assigns = when.conseq.collect{ case a: lir.Assign => a }
    val activeAssign = assigns.head
    assert(activeAssign.dst == lir.Reference(s"s1_fromSibling_$siblingHash$$_active", BackendType.bitTpe(1)(global)))
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
    val fromSubHash = extractHashCode("calledFromSub_([0-9a-f]+)\\$_active", fromSubName)

    val active = callParent.conseq.collectFirst{ case lir.Assign(lir.Reference(name, _), _) if name.contains("_active") => name }.get
    assert(active == s"top_calledFromSub_$fromSubHash$$_active")
  }

  test("module that is called from two indirect sibling modules") {
    val (modules, global) = untilThisPhase(Vector("test"), "Top", "callSiblingInterface1.tchdl")
    val top = findModule(modules, "Top").get
    val sub0 = findModule(modules, "Sub0").get
    val sub1 = findModule(modules, "Sub1").get
    val sub2 = findModule(modules, "Sub2").get

    val callName = sub0.procedures.collectFirst{ case lir.When(ref @ lir.Reference(name, _), _, _) if name.contains("call") => ref }.get
    val sub0Hash = extractHashCode("call_([0-9a-f]+)\\$_active", callName.name)
    val whens = top.procedures.collect{ case w: lir.When => w }
    val sub1Call = whens.collectFirst{ case w @ lir.When(lir.SubField(lir.Reference("sub1", _), _, _), _, _) => w }.get
    val sub2Call = whens.collectFirst{ case w @ lir.When(lir.SubField(lir.Reference("sub2", _), _, _), _, _) => w }.get
    val sub1sub0Assign = sub1Call.conseq.collectFirst{ case a @ lir.Assign(lir.SubField(_, name, _), _) if name.contains("_active") => a }.get
    val sub2sub0Assign = sub2Call.conseq.collectFirst{ case a @ lir.Assign(lir.SubField(_, name, _), _) if name.contains("_active") => a }.get

    assert(sub1sub0Assign.dst == lir.SubField(lir.Reference("sub0", sub0.tpe), s"call_$sub0Hash$$_active", BackendType.bitTpe(1)(global)))
    assert(sub2sub0Assign.dst == lir.SubField(lir.Reference("sub0", sub0.tpe), s"call_$sub0Hash$$_active", BackendType.bitTpe(1)(global)))
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

    assert(dst.name.matches("f_[0-9a-f]+\\$_ret"), dst.name)
    assert(src.name.matches("f_[0-9a-f]+\\$opt"), src.name)
  }

  test("construct hardware simple enum Option[Bit[2]]") {
    val (modules, global) = untilThisPhase(Vector("test"), "Mod", "ConstructEnum0.tchdl")
    val top = findModule(modules, "Mod").get

    val when = top.procedures.collect{ case when: lir.When => when }.head

    val initFieldName = when.conseq.collectFirst{ case node: lir.Node => node }.get
    val wire = when.conseq.collectFirst{ case wire: lir.Wire => wire }.get
    val connects = when.conseq.collect{ case connect: lir.Assign => connect }

    val temp = initFieldName.name
    val enum = wire.name
    val bit1 = toBackendType(Type.bitTpe(1)(global))(global)
    val bit2 = toBackendType(Type.bitTpe(2)(global))(global)
    val opt = wire.tpe

    assert(connects(0).dst == lir.SubField(lir.Reference(enum, opt), "_member", bit1))
    assert(connects(1).dst == lir.SubField(lir.Reference(enum, opt), "_data", bit2))

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
    assert(elems(5).isInstanceOf[lir.Assign])
    val opt = elems(6).asInstanceOf[lir.Assign].dst.asInstanceOf[lir.SubField].prefix.tpe
    assert(opt.symbol.name == "Opt")
    val dst = lir.SubField(lir.Reference("_ENUM_0", opt), "_data", bit32)
    val src = lir.Reference("_GEN_1", bit32)
    assert(elems(6) == lir.Assign(dst, src))
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

    assert(connect.dst == lir.SubField(lir.Reference("_ENUM_0", opt), "_member", bit1))
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
    val when = whens.find(_.cond.asInstanceOf[lir.Reference].name.matches("function1_[0-9a-f]+\\$_active")).get

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

  /*
  test("use state parameter with Future[Bit[8]]") {
    val (circuit, _) = untilThisPhase(Vector("test"), "Top", "useStateParam.tchdl")
    runFirrtl(circuit)
  }
   */

  /*
  test("use state parameter with Bit[8]") {
    val (circuit, _) = untilThisPhase(Vector("test"), "Top", "useStateParam1.tchdl")
    runFirrtl(circuit)
  }

  test("use state parameter for generate and relay") {
    val (circuit, _) = untilThisPhase(Vector("test"), "Top", "useStateParam2.tchdl")
    val stmts = circuit.modules
      .head.asInstanceOf[ir.Module]
      .body.asInstanceOf[ir.Block]
      .stmts

    val whens = stmts.collect{ case cond: ir.Conditionally => cond }
    val functionWhen = whens.find(_.pred.asInstanceOf[ir.Reference].name.contains("function")).get
    val s0When = whens.find(_.pred.asInstanceOf[ir.Reference].name.contains("s0")).get

    val functionName = functionWhen.pred.asInstanceOf[ir.Reference].name
    val s0Name = s0When.pred.asInstanceOf[ir.Reference].name

    val functionID = extractHashCode("function_([0-9a-f]+)\\$_active", functionName)
    val s0ID = extractHashCode("s0_([0-9a-f]+)\\$_active", s0Name)

    val connects = functionWhen.conseq.asInstanceOf[ir.Block].stmts.collect { case connect: ir.Connect => connect }
    assert(connects.length == 4)

    val connectX = connects(2)
    val connectY = connects(3)

    assert(connectX.loc == ir.Reference("s0_" + s0ID + "$st1$x", ir.UnknownType))
    assert(connectY.loc == ir.Reference("s0_" + s0ID + "$st1$y", ir.UnknownType))

    runFirrtl(circuit)
  }
  */

  /*
  test("method call with cast variable") {
    val (circuit, _) = untilThisPhase(Vector("test"), "Top", "castToCallMethod.tchdl")

    val ir.Connect(_, _, from) = circuit.modules
      .head.asInstanceOf[ir.Module]
      .body.asInstanceOf[ir.Block]
      .stmts
      .collectFirst{ case cond: ir.Conditionally => cond }.get
      .conseq.asInstanceOf[ir.Block]
      .stmts.last

    assert(from == ir.UIntLiteral(32, ir.IntWidth(32)))

    runFirrtl(circuit)
  }

  test("static method call with cast Type") {
    val (circuit, _) = untilThisPhase(Vector("test"), "Top", "castToSelectMethod.tchdl")
    runFirrtl(circuit)
  }

  test("call static method from type parameter with cast") {
    val (circuit, _) = untilThisPhase(Vector("test"), "Top", "castTPtoCallStatic.tchdl")
    runFirrtl(circuit)
  }

  test("call normal method from type parameter with cast") {
    val (circuit, _) = untilThisPhase(Vector("test"), "Top", "castTPtoCallNormal.tchdl")
    runFirrtl(circuit)
  }

  test("refer field type in function signature causes no error") {
    val (circuit, _) = untilThisPhase(Vector("test"), "Top", "referFieldTypeInSignature3.tchdl")

    runFirrtl(circuit)
  }

  test("use bit manipulation methods") {
    val (circuit, _) = untilThisPhase(Vector("test"), "Top", "useBitManipulationMethod.tchdl")
    runFirrtl(circuit)
  }

  test("read and write memory")  {
    val (circuit, _) = untilThisPhase(Vector("test"), "Top", "useMemory.tchdl")
    runFirrtl(circuit)
  }

  test("read registers by static and dynamic index") {
    val (circuit, _) = untilThisPhase(Vector("test"), "Top", "useVector.tchdl")
    runFirrtl(circuit)
  }

  test("write registers by assignment") {
    val (circuit, _) = untilThisPhase(Vector("test"), "Top", "useAssign.tchdl")
    runFirrtl(circuit)
  }

  test("use vector update") {
    val (circuit, _) = untilThisPhase(Vector("test"), "Top", "useVectorUpdate.tchdl")
    runFirrtl(circuit)
  }

  test("pattern match with bool type") {
    val (circuit, _) = untilThisPhase(Vector("test"), "Top", "PatternMatch9.tchdl")
    runFirrtl(circuit)
  }

  test("pattern match with Int type") {
    val (circuit, _) = untilThisPhase(Vector("test"), "Top", "PatternMatch10.tchdl")
    runFirrtl(circuit)
  }

  test("pattern match with Bit[2] type") {
    val (circuit, _) = untilThisPhase(Vector("test"), "Top", "PatternMatch11.tchdl")
    runFirrtl(circuit)
  }

  test("pattern match with Bit[2] type with ident catcher") {
    val (circuit, _) = untilThisPhase(Vector("test"), "Top", "PatternMatch12.tchdl")
    runFirrtl(circuit)
  }

  test("use cast method to cast some types into Bit[8]") {
    val (circuit, _) = untilThisPhase(Vector("test"), "Top", "useFroms.tchdl")
    runFirrtl(circuit)
  }

  test("compile grayscale module") {
    val (circuit, _) = untilThisPhase(Vector("lbp"), "GrayScaler", "RGB.tchdl", "GrayScaler.tchdl")
    runFirrtl(circuit)
  }

  test("update and refer multiple layer Vector") {
    val (circuit, _) = untilThisPhase(Vector("test"), "Top", "useVecVec.tchdl")
    runFirrtl(circuit)
  }

  test("use interface's internal interface") {
    val (circuit, _) = untilThisPhase(Vector("test"), "Top", "useInterfaceMethodForModule.tchdl")
    runFirrtl(circuit)
  }

  test("elaborate code that uses builder pattern") {
    val (circuit, _) = untilThisPhase(Vector("test"), "Top", "builderPattern.tchdl")
    runFirrtl(circuit)
  }

  test("use some vector manipulation methods") {
    val (circuit, _) = untilThisPhase(Vector("test"), "Top", "useVecManipulation.tchdl")
    runFirrtl(circuit)
  }

  test("use annotation to compile firrtl") {
    val (circuit, _) = untilThisPhase(Vector("test"), "Top", "useAllBinOpBit.tchdl")
    val emit = EmitCircuitAnnotation(classOf[VerilogEmitter])
    val compiler = new firrtl.stage.transforms.Compiler(firrtl.stage.Forms.VerilogOptimized)
    val init = CircuitState(circuit, Seq(emit))
    val state = compiler.execute(init)
    val emitter = new VerilogEmitter
    val result = emitter.execute(state)
    println(result.getEmittedCircuit.value)
  }
  */

  /*
  test("use future field in struct") {
    val (circuit, _) = untilThisPhase(Vector("test"), "Top", "partialFuture.tchdl")

    val outputs = circuit.modules.head.asInstanceOf[ir.Module].ports.filter(_.direction == ir.Output)
    assert(outputs.length == 2)

    runFirrtl(circuit)
  }

  test("use data structure with future field as stage parameter") {
    val (circuit, _) = untilThisPhase(Vector("test"), "Top", "partialFutureStage.tchdl")
    runFirrtl(circuit)
  }

  test("use partial future in sibling interface parameter") {
    val (circuit, _) = untilThisPhase(Vector("test"), "Top", "partialFutureSibling.tchdl")

    val topModule = circuit.modules.find(_.name == "test_Top").get.asInstanceOf[ir.Module]
    val sub0 = circuit.modules.find(_.name == "test_Sub0").get.asInstanceOf[ir.Module]
    val sub1 = circuit.modules.find(_.name == "test_Sub1").get.asInstanceOf[ir.Module]

    val called = sub1.body.asInstanceOf[ir.Block].stmts.collectFirst{ case c: ir.Conditionally => c.pred }.get.asInstanceOf[ir.Reference].name
    val calledHash = extractHashCode("called_([a-zA-Z0-9]+)\\$_active", called)
    val caller = sub0.body.asInstanceOf[ir.Block].stmts.collectFirst{ case c: ir.Conditionally => c }.get
    val callerHash = extractHashCode("caller_([a-zA-Z0-9]+)\\$_active", caller.pred.asInstanceOf[ir.Reference].name)

    val connects0 = topModule.body.asInstanceOf[ir.Block].stmts.collect{ case c: ir.Connect => c }.map(_.serialize)
    connects0.contains("""s1.called_""" + calledHash + """$st_b._member <= or(or(UInt<1>("h0"), s0.s1$called_""" + calledHash + """$st_b._member), s0.s1$called_""" + calledHash + """$st_b._member)""")
    connects0.contains("""s1.called_""" + calledHash + """$st_b._data <= or(or(UInt<1>("h0"), s0.s1$called_""" + calledHash + """$st_b._data), s0.s1$called_""" + calledHash + """$st_b._data)""")

    val expectCallerBody = caller.conseq.asInstanceOf[ir.Block].stmts.map(_.serialize)
    expectCallerBody.contains("""node _TEMP_3 = caller_""" + callerHash + """$st""")
    expectCallerBody.contains("""s1$called_""" + calledHash + """$_active <= UInt<1>("h1")""")
    expectCallerBody.contains("""s1$called_""" + calledHash + """$st <= _TEMP_3""")

    val connects1 = sub0.body.asInstanceOf[ir.Block].stmts.collect{ case c: ir.Connect => c }.map(_.serialize)
    connects1.contains("""_TEMP_3_b._member <= or(UInt<1>("h0"), caller_""" + callerHash + """$st_b._member)""")
    connects1.contains("""_TEMP_3_b._data <= or(UInt<1>("h0"), caller_""" + callerHash + """$st_b._data)""")

    runFirrtl(circuit)
  }

  test("use partial future in parent interface parameter") {
    val (circuit, _) = untilThisPhase(Vector("test"), "Top", "partialFutureParent.tchdl")

    val top = circuit.modules.find(_.name == "test_Top").get.asInstanceOf[ir.Module]
    val calledWires = top.body.asInstanceOf[ir.Block].stmts.collect{ case w: ir.DefWire => w }
    val wiresStr = calledWires.map(_.serialize)
    val connects = top.body.asInstanceOf[ir.Block].stmts.collect{ case c: ir.Connect => c }
    val connectStrs = connects.map(_.serialize)

    val active = calledWires.find(_.name.contains("active")).get

    val calledHash = extractHashCode("called_([a-zA-Z0-9]+)\\$_active", active.name)

    wiresStr.contains("""wire called_""" + calledHash + """$st : { a : UInt<4>}""")
    wiresStr.contains("""wire called_""" + calledHash + """$st_b : { _member : UInt<1>, _data : UInt<2>""")

    connectStrs.contains("""called_""" + calledHash + """$st_b._member <= or(or(UInt<1>("h0"), s0.top$called_""" + calledHash + """$st_b._member), s0.top$called_""" + calledHash + """$st_b._member)""")
    connectStrs.contains("""called_""" + calledHash + """$st_b._data <= or(or(UInt<1>("h0"), s0.top$called_""" + calledHash + """$st_b._data), s0.top$called_""" + calledHash + """$st_b._data)""")

    runFirrtl(circuit)
  }
  */
}
