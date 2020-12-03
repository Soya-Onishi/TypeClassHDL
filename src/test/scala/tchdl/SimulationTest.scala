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

@Slow
class SimulationTest extends TchdlFunSuite {
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

  test("very simple hardware") {
    val circuit = untilThisPhase(Vector("test"), "Top[4]", "OnlyTopThrowWire.tchdl")
    val top = circuit.modules.head.asInstanceOf[fir.Module]
    val topStmts = top.body.asInstanceOf[fir.Block].stmts
    val topPred = topStmts.collectFirst{ case fir.Conditionally(_, pred: fir.Reference, _, _) => pred }.get

    runSim(circuit) { tester =>
      for {
        v <- 0 to 15
      } yield {
        tester.poke(s"function__active", 1)
        tester.poke(s"function_in", v)
        tester.expect(s"function__ret", v)
      }
    }
  }

  test("use internal function which increment input value") {
    val circuit = untilThisPhase(Vector("test"), "Top", "InputCallInternalAdd.tchdl")
    val top = circuit.modules.head.asInstanceOf[fir.Module]
    val topStmts = top.body.asInstanceOf[fir.Block].stmts
    val pred = topStmts.collectFirst{ case fir.Conditionally(_, pred: fir.Reference, _, _) => pred }.get

    runSim(circuit) { tester =>
      for {
        v <- 0 to 255
      } yield {
        tester.poke(s"inputFunc__active", 1)
        tester.poke(s"inputFunc_in", v)
        tester.expect(s"inputFunc__ret", (v + 1) % 256)
      }
    }
  }

  test("use local variable in Top module") {
    val circuit = untilThisPhase(Vector("test"), "Top", "UseLocalVariableAdd.tchdl")
    val module = circuit.modules.head.asInstanceOf[fir.Module]

    runSim(circuit) { tester =>
      for {
        v <- 0 to 255
      } yield {
        tester.poke("func__active", 1)
        tester.poke("func_in", v)
        tester.expect("func__ret", (v + 1) % 256)
      }
    }
  }

  test("run ALU for complex value") {
    val circuit = untilThisPhase(Vector("test", "alu"), "Top", "ALUwithoutAlways.tchdl")
    val module = circuit.modules.find(_.name == "Top_0").get.asInstanceOf[fir.Module]
    val add = (n: String) => s"add_$n"
    val sub = (n: String) => s"sub_$n"

    info(circuit.serialize)

    runSim(circuit) { tester =>
      tester.poke("add__active", 1)
      tester.poke("sub__active", 1)

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
    val exec = (n: String) => s"exec_$n"
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
    val module = circuit.modules.find(_.name == "Top_0").get.asInstanceOf[fir.Module]
    val caller = (n: String) => s"caller_$n"
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
    val module = circuit.modules.find(_.name == "Top_0").get.asInstanceOf[fir.Module]
    val exec = (n: String) => s"execute_$n"
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
    val module = circuit.modules.find(_.name == "Top_0").get.asInstanceOf[fir.Module]
    val exec = (n: String) => s"execute_$n"
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
    val module = circuit.modules.find(_.name == "Top_0").get.asInstanceOf[fir.Module]
    val exec = (n: String) => s"execute_$n"
    val wait = (n: String) => s"waiting_$n"
    val procFirst = (n: String) => s"convolution_first_$n"
    val procSecond = (n: String) => s"convolution_second_$n"
    val rand = new Random(0)
    def next: Int = rand.nextInt(8)

    info(circuit.serialize)

    runSim(circuit) { tester =>
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

  test("use proc via sibling module") {
    val circuit = untilThisPhase(Vector("test"), "Top", "useProcViaSibling.tchdl")
    val module = circuit.modules.find(_.name == "Top_0").get.asInstanceOf[fir.Module]
    val call = (n: String) => s"caller_$n"
    val rand = new Random(0)
    def next: Int = rand.nextInt(255)

    info(circuit.serialize)

    runSim(circuit) { tester =>
      for {
        _ <- 0 to 255
      } yield {
        val pairs = Seq("a", "b", "c", "d").map(call).map(name => name -> next)
        tester.poke(call("_active"), 1)
        pairs.foreach{ case (name, value) => tester.poke(name, value) }

        val expect = pairs.foldLeft(0){ case (acc, (_, v)) => acc + v } % 256

        tester.step()
        tester.poke(call("_active"), 0)
        tester.step()
        tester.expect("out", expect)
        tester.step(2)
      }
    }
  }

  test("use proc via parent module") {
    val circuit = untilThisPhase(Vector("test"), "Top", "useProcViaParent.tchdl")
    val module = circuit.modules.find(_.name == "Top_0").get.asInstanceOf[fir.Module]
    val call = (n: String) => s"caller_$n"
    val rand = new Random(0)
    def next: Int = rand.nextInt(255)

    info(circuit.serialize)

    runSim(circuit) { tester =>
      for {
        _ <- 0 to 255
      } yield {
        val pairs = Seq("a", "b", "c", "d").map(call).map(name => name -> next)
        tester.poke(call("_active"), 1)
        pairs.foreach{ case (name, value) => tester.poke(name, value) }

        val expect = pairs.foldLeft(0){ case (acc, (_, v)) => acc + v } % 256

        tester.step()
        tester.poke(call("_active"), 0)
        tester.step()
        tester.expect("out", expect)
        tester.step(2)
      }
    }
  }

  test("construct complex struct") {
    val circuit = untilThisPhase(Vector("test"), "Top", "constructStruct.tchdl")
    val module = circuit.modules.find(_.name == "Top_0").get.asInstanceOf[fir.Module]
    val const = (n: String) => s"construct_$n"
    val rand = new Random(0)
    def next: Int = rand.nextInt(255)

    runSim(circuit) { tester =>
      for {
        _ <- 0 to 255
      } yield {
        val pairs = Seq("a", "b").map(const).map(_ -> next)
        tester.poke(const("_active"), 1)
        pairs.foreach{ case (name, value) => tester.poke(name, value)}

        val Seq(a, b) = pairs.map(_._2)
        tester.expect(const("_ret_real"), a)
        tester.expect(const("_ret_imag"), b)
      }
    }
  }

  test("simulate if expression") {
    val circuit = untilThisPhase(Vector("test"), "Top", "runIfExpr.tchdl")
    val module = circuit.modules.find(_.name == "Top_0").get.asInstanceOf[fir.Module]
    val select = (n: String) => s"select_$n"
    val rand = new Random(0)
    def next: Int = rand.nextInt(255)

    runSim(circuit) { tester =>
      for {
        flag <- 0 to 1
        _ <- 0 to 255
      } {
        val seq = Seq("a", "b").map(select).map(_ -> next)
        tester.poke(select("_active"), 1)
        seq.foreach{ case (name, value) => tester.poke(name, value) }
        tester.poke(select("flag"), flag)

        val Seq(a, b) = seq.map(_._2)
        val expect = if(flag == 1) a else b

        tester.expect(select("_ret"), expect)
      }
    }
  }

  test("relay another stage") {
    val circuit = untilThisPhase(Vector("test"), "Top", "relayAnotherStage.tchdl")
    val module = circuit.modules.find(_.name == "Top_0").get.asInstanceOf[fir.Module]
    val exec = (n: String) => s"execute_$n"
    val st0 = (n: String) => s"st0_$n"
    val st1 = (n: String) => s"st1_$n"
    val rand = new Random(0)
    def next: Int = rand.nextInt(255)

    runSim(circuit) { tester =>
      for {
        _ <- 0 to 255
      } {
        val seq = Seq("a", "b", "c", "d").map(exec).map(_ -> next)
        tester.poke(exec("_active"), 1)
        seq.foreach{ case (name, value) => tester.poke(name, value) }

        tester.step()

        tester.poke(exec("_active"), 0)
        tester.expect(st0("_active"), 1)
        tester.expect(st1("_active"), 0)

        tester.step()

        val expect = seq.map(_._2).foldLeft(0){ case (acc, v) => acc + v } % 256
        tester.expect(st0("_active"), 0)
        tester.expect(st1("_active"), 1)
        tester.expect("out", expect)

        tester.step()
      }
    }
  }

  test("cast type to use specific type class method") {
    val circuit = untilThisPhase(Vector("test"), "Top", "castTypeToTC.tchdl")
    val module = circuit.modules.find(_.name == "Top_0").get.asInstanceOf[fir.Module]
    val typeID = (n: String) => s"callTypeID_$n"
    val rawID = (n: String) => s"callRawID_$n"
    val rand = new Random(0)
    def next: Int = rand.nextInt(255)

    runSim(circuit) { tester =>
      for {
        _ <- 0 to 255
      } {
        val raw = next
        tester.poke(typeID("_active"), 1)
        tester.poke(typeID("in"), next)
        tester.poke(rawID("_active"), 1)
        tester.poke(rawID("in"), raw)

        tester.expect(typeID("_ret"), 1)
        tester.expect(rawID("_ret"), raw)

        tester.step()
      }
    }
  }

  test("procedure proc example code") {
    val circuit = untilThisPhase(Vector("test"), "Module", "TchdlProsProc.tchdl")
    val module = circuit.modules.find(_.name == "Module_0").get.asInstanceOf[fir.Module]
    val executeID = (n: String) => s"execute_$n"
    val receiveID = (n: String) => s"receiver_$n"
    val rand = new Random(0)
    def nextBool: Boolean = rand.nextBoolean()
    def nextBit8: Int = rand.nextInt(255)
    def calc(a: Int, b: Int, c: Int, d: Int)(f: (Int, Int) => Int): Int = {
      Vector(a, b, c, d).reduceLeft[Int]{ case (acc, x) => f(acc, x) & 255 }
    }

    // for simulation using convolutionAdd
    runSim(circuit) { tester =>
      for {
        _ <- 0 to 255
      } {
        val Vector(a, b, c, d) = Vector.fill(4)(nextBit8)
        val e = calc(a, b, c, d)(_ + _)

        tester.poke(executeID("useAdd"), 1)
        tester.poke(executeID("_active"), 1)
        tester.poke(executeID("a"), a)
        tester.poke(executeID("b"), b)
        tester.poke(executeID("c"), c)
        tester.poke(executeID("d"), d)

        tester.step()
        tester.poke(executeID("_active"), 0)
        tester.expect("out", 0)
        tester.expect(receiveID("_active"), 1)
        tester.step()
        tester.expect("out", e)
        tester.expect(receiveID("_active"), 1)
        tester.step()
        tester.expect(receiveID("_active"), 0)
        tester.step()
      }
    }

    runSim(circuit) { tester =>
      for {
        _ <- 0 to 255
      } {
        val Vector(a, b, c, d) = Vector.fill(4)(nextBit8)
        val e = calc(a, b, c, d)(_ - _)

        tester.poke(executeID("useAdd"), 0)
        tester.poke(executeID("_active"), 1)
        tester.poke(executeID("a"), a)
        tester.poke(executeID("b"), b)
        tester.poke(executeID("c"), c)
        tester.poke(executeID("d"), d)

        tester.step()
        tester.poke(executeID("_active"), 0)
        tester.expect("out", 0)
        tester.expect(receiveID("_active"), 1)

        tester.step()
        tester.expect("out", 0)
        tester.expect(receiveID("_active"), 1)

        tester.step()
        tester.expect("out", e)
        tester.expect(receiveID("_active"), 1)

        tester.step()

        tester.expect(receiveID("_active"), 0)
        tester.step()
      }
    }
  }

  test("run pattern matching sample") {
    val circuit = untilThisPhase(Vector("test"), "Top", "patternMatchSample.tchdl")
    val module = circuit.modules.find(_.name == "Top_0").get.asInstanceOf[fir.Module]
    val initID = (n: String) => s"initRegister_$n"
    val execID = (n: String) => s"execute_$n"
    val rand = new Random(0)
    def next: Int = rand.nextInt(255)

    val IMM = 0
    val REG = 1

    val ADD = 0
    val SUB = 1

    def combine(op0: Int, op0Data: Int, op1: Int, op1Data: Int): BigInt = {
      val flag0 = BigInt(op0)
      val data0 = BigInt(op0Data)
      val flag1 = BigInt(op1)
      val data1 = BigInt(op1Data)

      flag0 | (data0 << 1) | (flag1 << 9) | (data1 << 10)
    }

    def calc(op: Int, reg: Map[Int, Int], flags: Seq[Int], data: Seq[Int]): Int = {
      val f: (Int, Int) => Int = if(op == ADD) _ + _ else _ - _

      val operands = (flags zip data).map{ case (flag, data) => if(flag == IMM) data else reg(data) }

      f(operands(0), operands(1)) & 255
    }

    runSim(circuit, enableVcd = true) { tester =>
      tester.poke(initID(NameTemplate.active), 1)
      val initRegs = (0 until 16).map(_ -> next).toMap
      initRegs
        .map{ case (idx, v) => s"${initID("data")}_$idx" -> v }
        .foreach{ case (name, v) => tester.poke(name, v) }

      tester.step()

      tester.poke(initID(NameTemplate.active), 0)

      tester.step()

      for {
        _ <- 0 to 255
      } {
        val flags = Seq(REG, next % 2)
        val values = flags.map(flag => if(flag == IMM) next else next % 16)

        val op = next % 2
        tester.poke(execID(NameTemplate.active), 1)
        tester.poke(execID("opType"), op)
        tester.poke(execID("flag0"), flags(0))
        tester.poke(execID("flag1"), flags(1))
        tester.poke(execID("data0"), values(0))
        tester.poke(execID("data1"), values(1))

        val expect = calc(op, initRegs, flags, values)
        val actual = tester.peek(execID(NameTemplate.ret))

        tester.step()
        tester.expect(execID(NameTemplate.ret), expect)
      }
    }
  }

  test("input port with default value works correctly") {
    val circuit = untilThisPhase(Vector("test"), "Top", "portWithDefault.tchdl")
    def exec(name: String) = NameTemplate.concat("exec", name)
    val rnd = new Random(0)

    runSim(circuit) { tester =>
      for(_ <- 0 to 1000) {
        val value = rnd.nextInt(15)
        tester.poke(exec("in"), value)
        tester.poke(exec(NameTemplate.active), 1)

        tester.expect(exec(NameTemplate.ret), value)
      }

      for(_ <- 0 to 1000) {
        val value = rnd.nextInt(15)
        tester.poke(exec(NameTemplate.active), 0)
        tester.poke(exec("in"), value)

        tester.expect(exec(NameTemplate.ret), 0)
      }
    }
  }

  test("use ALU that accepts 4 commands") {
    val circuit = untilThisPhase(Vector("test"), "ALU", "useUserDefinedVariantID.tchdl")
    def exec(name: String) = NameTemplate.concat("execute", name)
    val rnd = new Random(0)

    runSim(circuit) { tester =>
      for{
        op <- 0 until   4
         _ <- 0    to 100
      } yield {
        val  a = BigInt(8, rnd)
        val b0 = BigInt(8, rnd)
        val  b = if(b0 == 0 && op == 3) BigInt(1) else b0
        val expect = op match {
          case 0 => (a + b) % 256
          case 1 => (a - b + 256) % 256
          case 2 => (a * b) % 256
          case 3 => (a / b) % 256
        }

        val bits = (b << 8) | a

        tester.poke(exec(NameTemplate.active), 1)
        tester.poke(exec(NameTemplate.concat("ops", NameTemplate.enumFlag)), op)
        tester.poke(exec(NameTemplate.concat("ops", NameTemplate.enumData)), bits)

        tester.expect(exec(NameTemplate.ret), expect)
      }
    }
  }

  test("use unary op for this.variable") {
    val rnd = new Random(0)
    val circuit = untilThisPhase(Vector("test"), "Top", "useNotForPort.tchdl")

    runSim(circuit) { tester =>
      for(_ <- 0 to 10) {
        val active = rnd.nextBoolean()
        val in = rnd.nextBoolean()

        tester.poke("__in_active", if(active) 1 else 0)
        tester.poke("__in_bits", if(in) 1 else 0)
        tester.expect("out", if(active & in) 0 else 1)
      }
    }
  }
}
