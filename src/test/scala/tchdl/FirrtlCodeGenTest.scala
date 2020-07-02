package tchdl

import tchdl.ast._
import tchdl.backend._
import tchdl.util._
import tchdl.typecheck._
import firrtl._
import firrtl.transforms._
import firrtl.passes._

import java.io.{File, FileWriter}
import java.nio.file.Files

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

  def runFirrtl(circuit: ir.Circuit): Unit = {
    val file = Files.createTempFile(null, ".fir")
    Files.write(file, circuit.serialize.getBytes)
    val circuitString = Files.readString(file)

    val command = Array("-i", file.toString)
    firrtl.stage.FirrtlMain.main(command)
  }

  test("build most simple code") {
    val (circuit, _) = untilThisPhase(Vector("test"), "Top[8]", "OnlyTopThrowWire.tchdl")

    val top = circuit.modules.find(_.name == "test_Top__8").get

    assert(top.ports.length == 5)
    assert(top.ports(0).name == "_CLK")
    assert(top.ports(1).name == "_RESET")
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

    // println(circuit.serialize)

    runFirrtl(circuit)
  }
}
