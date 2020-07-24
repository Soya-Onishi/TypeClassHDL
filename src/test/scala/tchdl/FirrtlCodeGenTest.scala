package tchdl

import tchdl.ast._
import tchdl.backend._
import tchdl.util._
import tchdl.typecheck._
import firrtl._

import java.nio.file.Files
import sys.process._
import scala.language.postfixOps

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

  def untilThisPhase(pkgName: Vector[String], module: String, names: String*): (ir.Circuit, GlobalData) = {
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
    expectNoError(newGlobal)

    val topModule = moduleContainers.head.tpe
    val circuit = FirrtlCodeGen.exec(topModule, moduleContainers, methodContainers)(newGlobal)

    (circuit, newGlobal)
  }

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

  test("build most simple code") {
    val (circuit, _) = untilThisPhase(Vector("test"), "Top[8]", "OnlyTopThrowWire.tchdl")

    val top = circuit.modules.find(_.name == "test_Top__8").get

    assert(top.ports.length == 5)
    assert(top.ports(0).name == "CLK")
    assert(top.ports(1).name == "RESET")
    assert(top.ports(2).name.matches("function_[0-9a-f]+\\$_active"))
    assert(top.ports(3).name.matches("function_[0-9a-f]+\\$in"))
    assert(top.ports(4).name.matches("function_[0-9a-f]+\\$_ret"))

    assert(top.ports(0).direction == ir.Input)
    assert(top.ports(1).direction == ir.Input)
    assert(top.ports(2).direction == ir.Input)
    assert(top.ports(3).direction == ir.Input)
    assert(top.ports(4).direction == ir.Output)

    assert(top.isInstanceOf[ir.Module])
    val topModule = top.asInstanceOf[ir.Module]
    val ir.Block(stmts) = topModule.body
    assert(stmts.length == 2)

    val invalid = stmts.head.asInstanceOf[ir.IsInvalid]
    assert(invalid.expr.isInstanceOf[ir.Reference])
    val ir.Reference(invalidTarget, _) = invalid.expr
    assert(invalidTarget.matches("function_[0-9a-f]+\\$_ret"), s"actual[$invalidTarget]")

    val condition = stmts.tail.head.asInstanceOf[ir.Conditionally]
    assert(condition.pred.isInstanceOf[ir.Reference])
    val ir.Reference(predName, _) = condition.pred
    assert(predName.matches("function_[0-9a-f]+\\$_active"), s"actual[$predName]")

    assert(condition.alt == ir.EmptyStmt)

    val ir.Block(conseqStmts) = condition.conseq
    assert(conseqStmts.length == 1)
    assert(conseqStmts.head.isInstanceOf[ir.Connect])
    val ir.Connect(_, ir.Reference(conseqRet, _), ir.Reference(conseqIn, _)) = conseqStmts.head
    assert(conseqRet.matches("function_[0-9a-f]+\\$_ret"))
    assert(conseqIn.matches("function_[0-9a-f]+\\$in"))

    runFirrtl(circuit)
  }

  test("input interface with Unit return type") {
    val (circuit, _) = untilThisPhase(Vector("test", "inner"), "Top", "InputUnitFunction.tchdl")
    val top = circuit.modules.find(_.name == "test_inner_Top").get

    assert(top.ports.length == 3)
    assert(top.ports(2).name.matches("f_[0-9a-f]+\\$_active"))

    val ir.Module(_, _, _, ir.Block(Seq(condition: ir.Conditionally))) = top
    assert(condition.conseq == ir.Block(Seq.empty))
    assert(condition.alt == ir.EmptyStmt)

    runFirrtl(circuit)
  }

  test("module that has internal interface and call it") {
    val (circuit, _) = untilThisPhase(Vector("test"), "Top", "InputCallInternal.tchdl")

    val top = circuit.modules.find(_.name == "test_Top").get.asInstanceOf[ir.Module]
    assert(top.ports.length == 5)
    assert(top.ports(2).name.matches("inputFunc_[0-9a-f]+\\$_active"))
    assert(top.ports(3).name.matches("inputFunc_[0-9a-f]+\\$in"))
    assert(top.ports(4).name.matches("inputFunc_[0-9a-f]+\\$_ret"))

    val body = top.body.asInstanceOf[ir.Block].stmts
    val wires = body.collect { case wire: ir.DefWire => wire }
    assert(wires.length == 3)
    assert(wires(0).name.matches("internalFunc_[0-9a-f]+\\$_active"))
    assert(wires(1).name.matches("internalFunc_[0-9a-f]+\\$x"))
    assert(wires(2).name.matches("internalFunc_[0-9a-f]+\\$_ret"))

    val conditionals = body.collect { case cond: ir.Conditionally => cond }
    val inputFunc = conditionals.head
    val internalFunc = conditionals.tail.head

    val ir.Reference(inputFuncPred, _) = inputFunc.pred
    val ir.Reference(internalFuncPred, _) = internalFunc.pred
    assert(inputFuncPred.matches("inputFunc_[0-9a-f]+\\$_active"))
    assert(internalFuncPred.matches("internalFunc_[0-9a-f]+\\$_active"))

    val internalFuncPattern = "internalFunc_([0-9a-f]+)\\$\\w+".r
    val internalFuncCode = internalFuncPattern.findAllIn(internalFuncPred).matchData.map{ _.group(1) }.toVector.head
    val retString = s"internalFunc_$internalFuncCode" + "$_ret"
    val xString = s"internalFunc_$internalFuncCode" + "$x"

    assert(internalFunc.conseq == ir.Block(
      ir.Connect(ir.NoInfo, ir.Reference(retString, ir.UnknownType), ir.Reference(xString, ir.UnknownType))
    ))
    assert(internalFunc.alt == ir.EmptyStmt)

    runFirrtl(circuit)
  }

  test("refer to local variable") {
    val (circuit, _) = untilThisPhase(Vector("test"), "Top", "UseLocalVariable.tchdl")

    val conseq = circuit.modules
      .find(_.name == "test_Top").get
      .asInstanceOf[ir.Module]
      .body.asInstanceOf[ir.Block]
      .stmts
      .collectFirst{ case cond: ir.Conditionally => cond }.get
      .conseq.asInstanceOf[ir.Block]
      .stmts

    val wire = conseq.head
    val connectLocal = conseq.tail.head
    val connectRet = conseq.tail.tail.head

    val funcCode = extractHashCode("func_([0-9a-f]+)\\$0\\$local_0", wire.asInstanceOf[ir.DefWire].name)
    val localName = concatNames("func", funcCode, "0", "local_0")
    val inName = concatNames("func", funcCode, "in")
    val retName = concatNames("func", funcCode, "_ret")

    assert(wire == ir.DefWire(ir.NoInfo, localName, ir.UIntType(ir.IntWidth(8))))
    assert(connectLocal == ir.Connect(
      ir.NoInfo,
      ir.Reference(localName, ir.UnknownType),
      ir.Reference(inName, ir.UnknownType)
    ))
    assert(connectRet == ir.Connect(
      ir.NoInfo,
      ir.Reference(retName, ir.UnknownType),
      ir.Reference(localName, ir.UnknownType)
    ))

    runFirrtl(circuit)
  }

  test("compile ALU circuit") {
    val (circuit, _) = untilThisPhase(Vector("test", "alu"), "Top", "ALU.tchdl")

    runFirrtl(circuit)
  }

  test("compile sequential circuit") {
    val (circuit, _) = untilThisPhase(Vector("test"), "M", "validSequenceCircuit.tchdl")

    runFirrtl(circuit)
  }

  test("compile ALU without always statement") {
    val (circuit, _) = untilThisPhase(Vector("test", "alu"), "Top", "ALUwithoutAlways.tchdl")

    runFirrtl(circuit)
  }

  test("module that calls sibling modules") {
    val (circuit, _) = untilThisPhase(Vector("test"), "Top", "useSiblingInterface.tchdl")
    runFirrtl(circuit)
  }

  test("module that call parent modules") {
    val (circuit, _) = untilThisPhase(Vector("test"), "Top", "callParentInterface0.tchdl")
    runFirrtl(circuit)
  }

  test("module that call indirect sibling modules") {
    val (circuit, _) = untilThisPhase(Vector("test"), "Top", "callSiblingInterface0.tchdl")
    runFirrtl(circuit)
  }

  test("module that call indirect parent module") {
    val (circuit, _) = untilThisPhase(Vector("test"), "Top", "callParentInterface1.tchdl")
    runFirrtl(circuit)
  }

  test("module that is called from two indirect sibling modules") {
    val (circuit, _) = untilThisPhase(Vector("test"), "Top", "callSiblingInterface1.tchdl")
    runFirrtl(circuit)
  }

  test("use enum type as interface's parameter type") {
    val (circuit, _) = untilThisPhase(Vector("test"), "Top", "enumWithInterfaceParam3.tchdl")

    val inputOpt = circuit.modules.head.ports.find(_.name.contains("opt")).get
    val outputRet = circuit.modules.head.ports.find(_.name.contains("_ret")).get

    assert(inputOpt.tpe == ir.BundleType(Seq(
      ir.Field("_member", ir.Default, ir.UIntType(ir.IntWidth(1))),
      ir.Field("_data", ir.Default, ir.UIntType(ir.IntWidth(8)))
    )))

    assert(outputRet.tpe == ir.BundleType(Seq(
      ir.Field("_member", ir.Default, ir.UIntType(ir.IntWidth(1))),
      ir.Field("_data", ir.Default, ir.UIntType(ir.IntWidth(8)))
    )))

    runFirrtl(circuit)
  }

  test("construct hardware simple enum Option[Bit[2]]") {
    val (circuit, _) = untilThisPhase(Vector("test"), "Mod", "ConstructEnum0.tchdl")

    val conseq = circuit.modules.head.asInstanceOf[ir.Module]
      .body.asInstanceOf[ir.Block]
      .stmts
      .collectFirst{ case cond: ir.Conditionally => cond }.get
      .conseq.asInstanceOf[ir.Block].stmts

    val initFieldName = conseq.collectFirst{ case node: ir.DefNode => node }.get
    val wire = conseq.collectFirst{ case wire: ir.DefWire => wire }.get
    val connects = conseq.collect{ case connect: ir.Connect => connect }

    val temp = initFieldName.name
    val enum = wire.name

    assert(connects(0).loc == ir.SubField(ir.Reference(enum, ir.UnknownType), "_member", ir.UnknownType))
    assert(connects(1).loc == ir.SubField(ir.Reference(enum, ir.UnknownType), "_data", ir.UnknownType))

    assert(connects(0).expr == ir.UIntLiteral(1))
    assert(connects(1).expr == ir.Reference(temp, ir.UnknownType))

    runFirrtl(circuit)
  }

  test("construct software simple enum Option[Int]") {
    val (circuit, _) = untilThisPhase(Vector("test"), "Mod", "ConstructEnum1.tchdl")

    val conseq = circuit.modules
      .head.asInstanceOf[ir.Module]
      .body.asInstanceOf[ir.Block]
      .stmts
      .collectFirst{ case cond: ir.Conditionally => cond }.get
      .conseq

    val elems = conseq.asInstanceOf[ir.Block].stmts
    assert(elems(0) == ir.DefNode(ir.NoInfo, "_TEMP_1", ir.UIntLiteral(1, ir.IntWidth(32))))
    assert(elems(3) == ir.Connect(ir.NoInfo, ir.SubField(ir.Reference("_ENUM_0", ir.UnknownType), "_data", ir.UnknownType), ir.Reference("_TEMP_1", ir.UnknownType)))

    runFirrtl(circuit)
  }

  test("construct hardware simple enum Option[Bit[2]]] however None") {
    val (circuit, _) = untilThisPhase(Vector("test"), "Mod", "ConstructEnum2.tchdl")

    val conseq = circuit.modules.head.asInstanceOf[ir.Module]
      .body.asInstanceOf[ir.Block]
      .stmts
      .collectFirst{ case cond: ir.Conditionally => cond }.get
      .conseq.asInstanceOf[ir.Block].stmts

    val connects = conseq.collect{ case connect: ir.Connect => connect }
    assert(connects(1).expr == ir.UIntLiteral(0))

    runFirrtl(circuit)
  }

  test("construct hardware complex enum three patterns") {
    val (circuit, _) = untilThisPhase(Vector("test"), "Top", "ConstructEnum3.tchdl")

    runFirrtl(circuit)
  }

  test("pattern match Option[Bit[2]] generates firrtl correctly") {
    val (circuit, _) = untilThisPhase(Vector("test"), "Top", "PatternMatch0.tchdl")
    runFirrtl(circuit)
  }

  test("pattern match Option[Bit[2]] but two Some pattern generates firrtl correctly") {
    val (circuit, _) = untilThisPhase(Vector("test"), "Top", "PatternMatch6.tchdl")
    runFirrtl(circuit)
  }

  test("pattern match Option[Int]") {
    val (circuit, _) = untilThisPhase(Vector("test"), "Top", "PatternMatch7.tchdl")
    runFirrtl(circuit)
  }

  test("stage with Future[Bit[_]] as return type must generate correct firrtl code") {
    val (circuit, _) = untilThisPhase(Vector("test"), "Top", "stageWithFuture.tchdl")
    runFirrtl(circuit)
  }

  test("stage with Future[Bit[2]] parameter") {
    val (circuit, _) = untilThisPhase(Vector("test"), "Top", "stageFutureParam.tchdl")
    runFirrtl(circuit)
  }

  test("stage with future pattern match causes no error") {
    val (circuit, _) = untilThisPhase(Vector("test"), "Top", "stageUseFuture.tchdl")

    val stmts = circuit.modules
      .head.asInstanceOf[ir.Module]
      .body.asInstanceOf[ir.Block]
      .stmts
      .toVector

    val connects = stmts
      .collect{ case connect: ir.Connect => connect }
      .collect{ case c @ ir.Connect(_, ir.SubField(ir.Reference(head, _), _, _), _) if head.matches("s3_[0-9a-f]+\\$_ret") => c }

    val member = connects.find{ case ir.Connect(_, ir.SubField(_, field, _), _) => field == "_member" }.get
    val data = connects.find{ case ir.Connect(_, ir.SubField(_, field, _), _) => field == "_data" }.get

    assert(member.expr.isInstanceOf[ir.DoPrim])
    assert(data.expr.isInstanceOf[ir.DoPrim])

    runFirrtl(circuit)
  }

  test("chained stage returns does not cause an error") {
    def findConnect(connects: Vector[ir.Connect], matches: String): Option[ir.Connect] =
      connects.collectFirst{
        case c @ ir.Connect(_, ir.SubField(ir.Reference(head, _), tail, _), _) if head.matches(matches) && tail == "_member" => c
      }

    def or(expr: ir.Expression): ir.DoPrim =
      ir.DoPrim(PrimOps.Or, Seq(ir.UIntLiteral(0), expr), Seq.empty, ir.UnknownType)

    val (circuit, _) = untilThisPhase(Vector("test"), "Top", "chainedStageFuture.tchdl")

    val stmts = circuit.modules
      .head.asInstanceOf[ir.Module]
      .body.asInstanceOf[ir.Block]
      .stmts
      .toVector

    val connects = stmts.collect{ case connect: ir.Connect => connect }

    val fRet = findConnect(connects, "function_[0-9a-f]+\\$_ret").get
    val s1Ret = findConnect(connects, "s1_[0-9a-f]+\\$_ret").get
    val s2Ret = findConnect(connects, "s2_[0-9a-f]+\\$_ret").get
    val enum = findConnect(connects, "_ENUM_[0-9]+").get

    assert(fRet.expr == or(s1Ret.loc))
    assert(s1Ret.expr == or(s2Ret.loc))
    assert(s2Ret.expr == or(enum.loc))
    assert(enum.expr == ir.UIntLiteral(0))

    runFirrtl(circuit)
  }

  test("call sibling interface with Future[_] parameter") {
    val (circuit, _) = untilThisPhase(Vector("test"), "Top", "CallSiblingFuture.tchdl")
    runFirrtl(circuit)
  }

  test("call parent interface with Future[_] parameter") {
    val (circuit, _) = untilThisPhase(Vector("test"), "Top", "CallParentFuture.tchdl")
    runFirrtl(circuit)
  }

  test("call all binary operation of Bit[_]") {
    val (circuit, _) = untilThisPhase(Vector("test"), "Top", "useAllBinOpBit.tchdl")
    runFirrtl(circuit)
  }

  test("call all binary operation of Int") {
    val (circuit, _) = untilThisPhase(Vector("test"), "Top", "useAllBinOpInt.tchdl")
    runFirrtl(circuit)
  }

  test("use state parameter with Future[Bit[8]]") {
    val (circuit, _) = untilThisPhase(Vector("test"), "Top", "useStateParam.tchdl")
    runFirrtl(circuit)
  }

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
    runFirrtl(circuit, print = true)
  }

  test("update and refer multiple layer Vector") {
    val (circuit, _) = untilThisPhase(Vector("test"), "Top", "useVecVec.tchdl")
    runFirrtl(circuit, print = true)
  }
}
