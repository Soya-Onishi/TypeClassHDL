package tchdl

import tchdl.ast._
import tchdl.parser._
import tchdl.typecheck._
import tchdl.backend._
import tchdl.util._

import firrtl.{ir => fir}
import firrtl.stage.FirrtlCircuitAnnotation
import treadle.TreadleTester

class SimulationTest extends TchdlFunSuite {
  def extractHashCode(regex: String, from: String): String = {
    val r = regex.r
    r.findAllIn(from).matchData.map{ _.group(1) }.toVector.head
  }

  def parse(filename: String): CompilationUnit =
    parseFile(_.compilation_unit)((gen, tree) => gen(tree, filename))(filename).asInstanceOf[CompilationUnit]

  def untilThisPhase(pkgName: Vector[String], module: String, names: String*): fir.Circuit = {
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

    circuit
  }

  private def runSim(circuit: fir.Circuit)(f: TreadleTester => Unit): Unit = {
    val annon = FirrtlCircuitAnnotation(circuit)
    val tester = TreadleTester(Seq(annon))

    f(tester)

    if(tester.isOK) info(tester.reportString)
    else fail(tester.reportString)
  }

  private def getNameGenFromMethod(module: fir.Module, methodName: String): String => String = {
    val stmts = module.body.asInstanceOf[fir.Block].stmts
    val conds = stmts.collect{ case c: fir.Conditionally => c }
    val predRefs = conds.map(_.pred).collect{ case r: fir.Reference => r }

    val hashCode = predRefs.find(_.name.matches(s"${methodName}_[0-9a-f]+\\$$_active"))
      .map(_.name)
      .map(name => extractHashCode(s"${methodName}_([0-9a-f]+)\\$$_active", name))
      .get

    (name: String) => s"${methodName}_$hashCode$$$name"
  }

  test("very simple hardware") {
    val circuit = untilThisPhase(Vector("test"), "Top[4]", "OnlyTopThrowWire.tchdl")
    val top = circuit.modules.head.asInstanceOf[fir.Module]
    val topStmts = top.body.asInstanceOf[fir.Block].stmts
    val topPred = topStmts.collectFirst{ case fir.Conditionally(_, pred: fir.Reference, _, _) => pred }.get
    val hashCode = extractHashCode("function_([0-9a-f]+)\\$_active", topPred.name)

    runSim(circuit) { tester =>
      for {
        v <- 0 to 15
      } yield {
        tester.poke(s"function_$hashCode$$_active", 1)
        tester.poke(s"function_$hashCode$$in", v)
        tester.expect(s"function_$hashCode$$_ret", v)
      }
    }
  }

  test("use internal function which increment input value") {
    val circuit = untilThisPhase(Vector("test"), "Top", "InputCallInternalAdd.tchdl")
    val top = circuit.modules.head.asInstanceOf[fir.Module]
    val topStmts = top.body.asInstanceOf[fir.Block].stmts
    val pred = topStmts.collectFirst{ case fir.Conditionally(_, pred: fir.Reference, _, _) => pred }.get
    val hashCode = extractHashCode("inputFunc_([0-9a-f]+)\\$_active", pred.name)

    runSim(circuit) { tester =>
      for {
        v <- 0 to 255
      } yield {
        tester.poke(s"inputFunc_$hashCode$$_active", 1)
        tester.poke(s"inputFunc_$hashCode$$in", v)
        tester.expect(s"inputFunc_$hashCode$$_ret", (v + 1) % 256)
      }
    }
  }

  test("use local variable in Top module") {
    val circuit = untilThisPhase(Vector("test"), "Top", "UseLocalVariableAdd.tchdl")
    val module = circuit.modules.head.asInstanceOf[fir.Module]
    val name = getNameGenFromMethod(module, "func")

    runSim(circuit) { tester =>
      for {
        v <- 0 to 255
      } yield {
        tester.poke(name("_active"), 1)
        tester.poke(name("in"), v)
        tester.expect(name("_ret"), (v + 1) % 256)
      }
    }
  }

  test("run ALU for complex value") {
    val circuit = untilThisPhase(Vector("test", "alu"), "Top", "ALUwithoutAlways.tchdl")
    val module = circuit.modules.find(_.name == "Top").get.asInstanceOf[fir.Module]
    val add = getNameGenFromMethod(module, "add")
    val sub = getNameGenFromMethod(module, "sub")

    println(circuit.serialize)

    runSim(circuit) { tester =>
      tester.poke(add("_active"), 1)
      tester.poke(sub("_active"), 1)

      for {
        aReal <- 0 to 16
        aImag <- 0 to 16
        bReal <- 0 to 16
        bImag <- 0 to 16
      } yield {
        tester.poke(add("a_real"), aReal)
        tester.poke(add("a_imag"), aImag)
        tester.poke(add("b_real"), bReal)
        tester.poke(add("b_imag"), bImag)

        tester.poke(sub("a_real"), aReal)
        tester.poke(sub("a_imag"), aImag)
        tester.poke(sub("b_real"), bReal)
        tester.poke(sub("b_imag"), bImag)

        tester.expect(add("_ret_real"), (aReal + bReal) % 256)
        tester.expect(add("_ret_imag"), (aImag + bImag) % 256)
        tester.expect(sub("_ret_real"), ((aReal - bReal) + 256) % 256)
        tester.expect(sub("_ret_imag"), ((aImag - bImag) + 256) % 256)
      }
    }
  }
}
