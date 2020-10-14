package tchdl

import tchdl.ast._
import tchdl.parser._
import tchdl.typecheck._
import tchdl.backend._
import tchdl.util._

import firrtl.{ir => fir}
import firrtl.stage.FirrtlCircuitAnnotation
import treadle.TreadleTester

import java.util.Random
import org.scalatest.tags.Slow

@Slow
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

  private def runSim(circuit: fir.Circuit, enableVcd: Boolean = false)(f: TreadleTester => Unit): Unit = {
    val clockInfo = treadle.executable.ClockInfo("CLK")
    val annons = Seq(
      treadle.ClockInfoAnnotation(Seq(clockInfo)),
      treadle.ResetNameAnnotation("RST"),
      FirrtlCircuitAnnotation(circuit)
    )
    val passedAnnons =
      if(enableVcd) annons :+ treadle.WriteVcdAnnotation
      else annons

    val tester = TreadleTester(passedAnnons)

    f(tester)

    if(tester.finish) info(tester.reportString)
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

  private def getNameGenFromProc(module: fir.Module, proc: String, block: String): String => String = {
    val stmts = module.body.asInstanceOf[fir.Block].stmts
    val conds = stmts.collect{ case c: fir.Conditionally => c }
    val predRefs = conds.map(_.pred).collect{ case r: fir.Reference => r }

    val hashCode = predRefs.find(_.name.matches(s"${proc}_[0-9a-f]+_$block\\$$_active"))
      .map(_.name)
      .map(name => extractHashCode(s"${proc}_([0-9a-f]+)_$block\\$$_active", name))
      .get

    (name: String) => s"${proc}_${hashCode}_$block$$$name"
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

    info(circuit.serialize)

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

  test("stage multiple add") {
    val circuit = untilThisPhase(Vector("test"), "Top", "stageMultAdd.tchdl")
    val top = circuit.modules.head.asInstanceOf[fir.Module]
    val exec = getNameGenFromMethod(top, "exec")
    val rand = new Random(0)
    def next: Int = rand.nextInt(255)

    runSim(circuit) { tester =>
      for {
        _ <- 0 to 255
      } yield {
        val seqs = Vector("a", "b", "c", "d").map(name => exec(name) -> next)
        seqs.foreach { case (name, value) => tester.poke(name, value) }

        tester.poke(exec("_active"), 1)
        tester.step()
        tester.poke(exec("_active"), 0)
        tester.step()

        val expect = seqs.map(_._2).foldLeft(0){ case (acc, x) => acc + x } % 256
        tester.expect("result", expect)
      }
    }
  }

  test("using type parameter and doing add as T type works correctly") {
    val circuit = untilThisPhase(Vector("test"), "Top", "useTypeParamAndNormal.tchdl")
    val rand = new Random(0)

    runSim(circuit) { tester =>
      for {
        _ <- 0 to 255
      } yield {
        val bit4s = Vector("aBit4", "bBit4").map(name => name -> rand.nextInt(15))
        val bit8s = Vector("aBit8", "bBit8").map(name => name -> rand.nextInt(255))

        bit4s.foreach{ case (name, value) => tester.poke(name, value) }
        bit8s.foreach{ case (name, value) => tester.poke(name, value) }

        val bit4Expect = (bit4s(0)._2 + bit4s(1)._2) % 16
        val bit8Expect = (bit8s(0)._2 + bit8s(1)._2) % 256
        tester.expect("outBit4", bit4Expect)
        tester.expect("outBit8", bit8Expect)
        tester.expect("outTBit4", bit4Expect)
        tester.expect("outTBit8", bit8Expect)

        tester.step(1)
      }
    }
  }

  test("use sibling feature") {
    val circuit = untilThisPhase(Vector("test"), "Top", "useSiblingToAdd.tchdl")
    val module = circuit.modules.find(_.name == "Top").get.asInstanceOf[fir.Module]
    val caller = getNameGenFromMethod(module, "caller")
    val rand = new Random(0)

    info(circuit.serialize)

    runSim(circuit) { tester =>
      for {
        _ <- 0 to 255
      } yield {
        val value = rand.nextInt(255)
        val operand = rand.nextInt(255)
        tester.poke(caller("_active"), 1)
        tester.poke(caller("value"), value)
        tester.poke("sub1Operand", operand)

        tester.expect(caller("_ret"), (value + operand) % 256)
        tester.step()
        tester.poke(caller("_active"), 0)
        tester.step()
      }
    }
  }

  test("use parent feature") {
    val circuit = untilThisPhase(Vector("test"), "Top", "useParentToAdd.tchdl")
    val module = circuit.modules.find(_.name == "Top").get.asInstanceOf[fir.Module]
    val exec = getNameGenFromMethod(module, "execute")
    val rand = new Random(0)

    runSim(circuit) { tester =>
      for {
         _ <- 0 to 255
      } yield {
        val value = rand.nextInt(255)
        val operand = rand.nextInt(255)

        tester.poke(exec("_active"), 1)
        tester.poke(exec("value"), value)
        tester.poke("operand", operand)

        val expect = (value + operand) % 256
        tester.expect(exec("_ret"), expect)

        tester.step()
        tester.poke(exec("_active"), 0)
        tester.step()
      }
    }
  }

  test("use enum and pattern matching") {
    val circuit = untilThisPhase(Vector("test"), "Top", "useEnumMatching.tchdl")
    val module = circuit.modules.find(_.name == "Top").get.asInstanceOf[fir.Module]
    val exec = getNameGenFromMethod(module, "execute")
    val rand = new Random(0)

    info(circuit.serialize)

    runSim(circuit) { tester =>
      for {
        _ <- 0 to 255
      } yield {
        val value = rand.nextInt(15)
        val member = rand.nextInt(1)

        tester.poke(exec("_active"), 1)
        tester.poke(exec("in__member"), member)
        tester.poke(exec("in__data"), value)

        val expect =
          if(member == 1) (value + 1) % 16
          else 0
        tester.expect(exec("_ret"), expect)

        tester.step()
        tester.poke(exec("_active"), 0)
        tester.step()
      }
    }
  }

  test("use register with init value and increment each cycle") {
    val circuit = untilThisPhase(Vector("test"), "Top", "useRegister.tchdl")

    runSim(circuit) { tester =>
      for {
        expect <- 0 to 512
      } yield {
        tester.expect("out", expect % 256)
        tester.step()
      }
    }
  }

  test("use simple proc and deref in stage block") {
    val circuit = untilThisPhase(Vector("test"), "Top", "useProcAndDeref.tchdl")
    val module = circuit.modules.find(_.name == "Top").get.asInstanceOf[fir.Module]
    val exec = getNameGenFromMethod(module, "execute")
    val wait = getNameGenFromMethod(module, "waiting")
    val procFirst = getNameGenFromProc(module, "convolution", "first")
    val procSecond = getNameGenFromProc(module, "convolution", "second")
    val rand = new Random(0)
    def next: Int = rand.nextInt(8)

    info(circuit.serialize)

    runSim(circuit, enableVcd = true) { tester =>
      for {
        _ <- 0 to 255
      } yield {
        val ports = Seq("a", "b", "c", "d")
        val pairs = ports.map(exec).map(name => name -> next)
        tester.poke(exec("_active"), 1)
        pairs.foreach{ case (name, value) => tester.poke(name, value) }

        val expect = pairs.foldLeft(0){ case (acc, (_, v)) => acc + v } % 256

        tester.step()
        tester.poke(exec("_active"), 0)
        tester.step()
        tester.expect("out", expect)
        tester.step()
        tester.expect(procFirst("_active"), 0)
        tester.expect(procSecond("_active"), 0)
        tester.expect(wait("_active"), 0)
        tester.step()
      }
    }
  }
}
