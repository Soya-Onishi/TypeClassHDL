package tchdl

import tchdl.ast._
import tchdl.backend._
import tchdl.util._
import tchdl.typecheck._

import firrtl.ir
import firrtl._
import firrtl.transforms._
import firrtl.passes._

class FirrtlCodeGenTest extends TchdlFunSuite {
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

  def transform(circuit: ir.Circuit): ir.Circuit = {
    val state = CircuitState(circuit, Seq.empty)

    // Designate a series of transforms to be run in this order
    val transforms = Seq(
      ToWorkingIR,
      ResolveKinds,
      InferTypes,
      ResolveFlows,
      InferWidths(),
      new ConstantPropagation)

    // Run transforms and capture final state
    val finalState = transforms.foldLeft(state) {
      (c: CircuitState, t: Transform) => t.runTransform(c)
    }

    finalState.circuit
  }

  test("build most simple code") {
    val (circuit, _) = untilThisPhase(Vector("test"), "Top[8]", "OnlyTopThrowWire.tchdl")

    val top = circuit.modules.find(_.name == "test_Top__8").get

    assert(top.ports.length == 3)
    assert(top.ports(0).name == "function$active")
    assert(top.ports(1).name == "function$in")
    assert(top.ports(2).name == "function$ret")

    assert(top.ports(0).direction == ir.Input)
    assert(top.ports(1).direction == ir.Input)
    assert(top.ports(2).direction == ir.Output)

    val ir.Module(_, _, _, body) = top
    assert(top.isInstanceOf[ir.Module])
    val topModule = top.asInstanceOf[ir.Module]
    val ir.Block(stmts) = topModule.body
    assert(stmts.length == 2)

    val invalid = stmts.head.asInstanceOf[ir.IsInvalid]
    assert(invalid.expr == ir.Reference("function$ret", ir.UnknownType))

    val condition = stmts.tail.head.asInstanceOf[ir.Conditionally]
    assert(condition.pred == ir.Reference("function$active", ir.UnknownType))
    assert(condition.alt == ir.EmptyStmt)

    val ir.Block(conseqStmts) = condition.conseq
    assert(conseqStmts.length == 1)
    assert(conseqStmts.head == ir.Connect(ir.NoInfo, ir.Reference("function$ret", ir.UnknownType), ir.Reference("function$in", ir.UnknownType)))

    transform(circuit)
  }

  test("input interface with Unit return type") {
    val (circuit, _) = untilThisPhase(Vector("test", "inner"), "Top", "InputUnitFunction.tchdl")
    val top = circuit.modules.find(_.name == "test_inner_Top").get

    assert(top.ports.length == 1)
    assert(top.ports.head.name == "f$active")

    val ir.Module(_, _, _, ir.Block(Seq(condition: ir.Conditionally))) = top
    assert(condition.conseq == ir.Block(Seq.empty))
    assert(condition.alt == ir.EmptyStmt)

    transform(circuit)
  }

  test("module that has internal interface and call it") {
    val (circuit, _) = untilThisPhase(Vector("test"), "Top", "InputCallInternal.tchdl")

    val top = circuit.modules.find(_.name == "test_Top").get.asInstanceOf[ir.Module]
    assert(top.ports.length == 3)
    assert(top.ports(0).name == "inputFunc$active")
    assert(top.ports(1).name == "inputFunc$in")
    assert(top.ports(2).name == "inputFunc$ret")

    val body = top.body.asInstanceOf[ir.Block].stmts
    val wires = body.collect { case wire: ir.DefWire => wire }
    assert(wires.length == 3)
    assert(wires(0).name == "internalFunc$active")
    assert(wires(1).name == "internalFunc$x")
    assert(wires(2).name == "internalFunc$ret")

    val conditionals = body.collect { case cond: ir.Conditionally => cond }
    val inputFunc = conditionals.head
    val internalFunc = conditionals.tail.head

    assert(inputFunc.pred == ir.Reference("inputFunc$active", ir.UnknownType))
    assert(internalFunc.pred == ir.Reference("internalFunc$active", ir.UnknownType))
    assert(internalFunc.conseq == ir.Block(
      ir.Connect(ir.NoInfo, ir.Reference("internalFunc$ret", ir.UnknownType), ir.Reference("internalFunc$x", ir.UnknownType))
    ))
    assert(internalFunc.alt == ir.EmptyStmt)

    transform(circuit)
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

    assert(wire == ir.DefWire(ir.NoInfo, "func$0$local_0", ir.UIntType(ir.IntWidth(8))))
    assert(connectLocal == ir.Connect(
      ir.NoInfo,
      ir.Reference("func$0$local_0", ir.UnknownType),
      ir.Reference("func$in", ir.UnknownType)
    ))
    assert(connectRet == ir.Connect(
      ir.NoInfo,
      ir.Reference("func$ret", ir.UnknownType),
      ir.Reference("func$0$local_0", ir.UnknownType)
    ))

    transform(circuit)
  }

  test("compile ALU circuit") {
    val (circuit, _) = untilThisPhase(Vector("test", "alu"), "Top", "ALU.tchdl")

    transform(circuit)
  }
}
