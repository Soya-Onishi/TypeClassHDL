package tchdl

import tchdl.ast._
import tchdl.parser._
import tchdl.typecheck._
import tchdl.backend._
import tchdl.util._

import firrtl.{ir => fir}
import firrtl.stage.FirrtlCircuitAnnotation
import firrtl.transforms.NoDCEAnnotation
import treadle.TreadleTester

import java.util.Random
import org.scalatest.tags.Slow

class RiscvTest extends TchdlFunSuite {
  def parse(filename: String): CompilationUnit =
    parseFile(_.compilation_unit)((gen, tree) => gen(tree, filename))(filename).asInstanceOf[CompilationUnit]

  def untilThisPhase(pkgName: Vector[String], module: String, names: String*): fir.Circuit = {
    val filePath = "src/test/riscv"
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

  private def runSim(circuit: fir.Circuit, enableVcd: Boolean = false)(f: TreadleTester => Unit): Unit = {
    val clockInfo = treadle.executable.ClockInfo("CLK")
    val annons = Seq(
      treadle.ClockInfoAnnotation(Seq(clockInfo)),
      treadle.ResetNameAnnotation("RST"),
      FirrtlCircuitAnnotation(circuit),
      NoDCEAnnotation
    )
    val passedAnnons =
      if(enableVcd) annons :+ treadle.WriteVcdAnnotation
      else annons

    val tester = TreadleTester(passedAnnons)

    f(tester)

    if(tester.finish) info(tester.reportString)
    else fail(tester.reportString)
  }

  test("register file unit test") {
    val rnd = new Random(0)
    val circuit = untilThisPhase(Vector("riscv"), "RegisterFile", "RegisterFile.tchdl")
    val seq = Seq.fill(32)(BigInt(32, rnd))

    runSim(circuit) { tester =>
      tester.poke("rs1__active", 0)
      tester.poke("rs2__active", 0)
      tester.poke("write__active", 0)
      tester.step(1)

      for (idx <- 0 until 32) {
        val v = seq(idx)
        tester.poke("write__active", 1)
        tester.poke("write_addr", idx)
        tester.poke("write_data", v)
        tester.step(1)
      }

      tester.step(1)

      for{
        port <- Seq("rs1_", "rs2_")
        idx <- 0 until 32
      } {
        tester.poke(port + "_active", 1)
        tester.poke(port + "addr", idx)

        val expect = if(idx == 0) BigInt(0) else seq(idx)
        tester.expect(port + "_ret", expect)
        tester.step(1)
      }
    }
  }


}
