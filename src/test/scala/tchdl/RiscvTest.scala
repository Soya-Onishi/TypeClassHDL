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
    assert(global.repo.error.counts == 0, showErrorsSimple(global))

    trees.foreach(NamerPost.exec)
    assert(global.repo.error.counts == 0, showErrorsSimple(global))

    trees.foreach(BuildImplContainer.exec)
    assert(global.repo.error.counts == 0, showErrorsSimple(global))

    VerifyImplConflict.verifyImplConflict()
    assert(global.repo.error.counts == 0, showErrorsSimple(global))

    val trees0 = trees.map(TopDefTyper.exec)
    assert(global.repo.error.counts == 0, showErrorsSimple(global))

    trees0.foreach(ImplMethodSigTyper.exec)
    assert(global.repo.error.counts == 0, showErrorsSimple(global))

    val trees1 = trees0.map(Typer.exec)
    assert(global.repo.error.counts == 0, showErrorsSimple(global))

    trees1.foreach(RefCheck.exec)
    assert(global.repo.error.counts == 0, showErrorsSimple(global))

    val newGlobal = global.assignCompilationUnits(trees1.toVector)
    val modules = BuildGeneratedModuleList.exec(newGlobal)
    assert(newGlobal.repo.error.counts == 0, showErrorsSimple(newGlobal))

    val (moduleContainers, methodContainers) = BackendIRGen.exec(modules)(newGlobal)
    assert(newGlobal.repo.error.counts == 0, showErrorsSimple(newGlobal))

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

  test("comparator unit test") {
    val rnd = new Random(0)
    val circuit = untilThisPhase(Vector("riscv"), "Comparator", "Comparator.tchdl", "Types.tchdl")
    def next = BigInt(32, rnd)

    def lt(a: BigInt, b: BigInt): Boolean = {
      val tmp0 = a ^ (BigInt(1) << 31)
      val tmp1 = b ^ (BigInt(1) << 31)
      val comp = (tmp0 - tmp1) & (BigInt(1) << 32)

      comp != 0
    }

    def ge(a: BigInt, b: BigInt): Boolean = lt(b, a)

    runSim(circuit) { tester =>
      val ops: Seq[(BigInt, BigInt) => Boolean] = Seq(_ == _, _ != _, lt, ge, _ < _, _ >= _)

      for{
        (op, rawOp) <- ops.zipWithIndex
        _ <- 0 to 1000
      } {
        val a = next
        val b = next
        val v = (b << 32) | a

        tester.poke("execute__active", 1)
        tester.poke("execute_op__member", rawOp)
        tester.poke("execute_op__data", v)

        val expect = if(op(a, b)) 1 else 0
        tester.expect("execute__ret", expect)
      }
    }
  }

  test("unit test of forwarding unit") {
    val rnd = new Random(0)
    val circuit = untilThisPhase(Vector("riscv"), "ForwardingUnit", "ForwardingUnit.tchdl", "Types.tchdl")
    def next = BigInt(32, rnd)

    def setRs(interface: String, addr: BigInt, data: BigInt, tester: TreadleTester): BigInt = {
      def nme(name: String): String = NameTemplate.concat(interface, name)

      tester.poke(nme(NameTemplate.active), 1)
      tester.poke(nme("addr"), addr)
      tester.poke(nme("data"), data)
      tester.peek(nme(NameTemplate.ret))
    }
    def hazard(name: String): String = NameTemplate.concat("isLoadHazard", name)
    def forward(stage: String, isSome: Boolean, rd: BigInt, data: BigInt, tester: TreadleTester): Unit = {
      val prefix = s"__$stage"
      val rdName = s"${prefix}Rd"
      val dataName = s"${prefix}Data"

      tester.poke(s"${rdName}_active", 1)
      tester.poke(s"${rdName}_bits__member", if(isSome) 1 else 0)
      tester.poke(s"${rdName}_bits__data", rd)
      tester.poke(s"${dataName}_active", 1)
      tester.poke(s"${dataName}_bits__member", if(isSome) 1 else 0)
      tester.poke(s"${dataName}_bits__data", data)
    }
    def disable(stage: String, tester: TreadleTester): Unit = {
      val prefix = s"__$stage"
      val rdName = s"${prefix}Rd"
      val dataName = s"${prefix}Data"

      tester.poke(s"${rdName}_active", 0)
      tester.poke(s"${dataName}_active", 0)
    }

    def execute(infos: Seq[(Boolean, BigInt, BigInt)], name: String, tester: TreadleTester): Unit = {
      val addr = next % 32
      val data = if(addr == 0) BigInt(0) else next
      setRs(name, addr, data, tester)
      val expect =
        if(addr == 0) BigInt(0)
        else infos.filter(_._1)
          .find(_._2 == addr)
          .map{ case (_, _, data) => data }
          .getOrElse(data)

      val message =
        s"""
           |exe: active(${infos(0)._1}), rd(${infos(0)._2}), data(${infos(0)._3})
           |mem: active(${infos(1)._1}), rd(${infos(1)._2}), data(${infos(1)._3})
           | wb: active(${infos(2)._1}), rd(${infos(2)._2}), data(${infos(2)._3})
           |act: rd($addr), data($data)
           |""".stripMargin

      tester.expect(
        NameTemplate.concat(name, NameTemplate.ret),
        expect,
        message
      )
    }

    runSim(circuit) { tester =>
      disable("exec", tester)
      disable("mem", tester)
      disable("wb", tester)
      tester.poke("__isExeLoad_active", 0)
      tester.poke("__isMemLoad_active", 0)
      tester.poke("__isLoadDone_active", 0)
      tester.poke(NameTemplate.concat("rs1", NameTemplate.active), 0)
      tester.poke(NameTemplate.concat("rs2", NameTemplate.active), 0)
      tester.poke(hazard(NameTemplate.active), 0)

      for(_ <- 0 to 100000) {
        val execForward = rnd.nextBoolean()
        val memForward = rnd.nextBoolean()
        val wbForward = rnd.nextBoolean()
        val forwardFlags = Seq(execForward, memForward, wbForward)

        val tuples = (forwardFlags zip Seq("exec", "mem", "wb")).map {
          case (bool, name) =>
            val rd = next % 32
            val data = next

            if(bool) forward(name, isSome = true, rd, data, tester)
            else disable(name, tester)

            (rd, data)
        }

        val infos = (forwardFlags zip tuples).map{ case (flag, (rd, data)) => (flag, rd, data) }
        execute(infos, "rs1", tester)
        execute(infos, "rs2", tester)

        val execLoad = rnd.nextBoolean() && infos(0)._1
        val memLoad = rnd.nextBoolean() && infos(1)._1
        val loadDone = memLoad & rnd.nextBoolean()
        val rs1Addr = next % 32
        val rs2Addr = next % 32
        tester.poke("__isExeLoad_active", 1)
        tester.poke("__isMemLoad_active", 1)
        tester.poke("__isLoadDone_active", 1)
        tester.poke("__isExeLoad_bits", if(execLoad) 1 else 0)
        tester.poke("__isMemLoad_bits", if(memLoad) 1 else 0)
        tester.poke("__isLoadDone_bits", if(loadDone) 1 else 0)
        tester.poke("isLoadHazard__active", 1)
        tester.poke("isLoadHazard_rs1", rs1Addr)
        tester.poke("isLoadHazard_rs2", rs2Addr)

        val exeHazard = infos(0)._1 && (infos(0)._2 == rs1Addr || infos(0)._2 == rs2Addr) && execLoad
        val memHazard = infos(1)._1 && (infos(1)._2 == rs1Addr || infos(1)._2 == rs2Addr) && memLoad && !loadDone
        tester.expect("isLoadHazard__ret", if(exeHazard | memHazard) 1 else 0)

        tester.step(1)
      }
    }
  }

  test("BarrelShifter unit test") {
    val rnd = new Random(0)
    def next(width: Int): BigInt = BigInt(width, rnd)
    val circuit = untilThisPhase(Vector("riscv"), "BarrelShifter", "BarrelShifter.tchdl", "Types.tchdl")

    def exec(name: String*): String = NameTemplate.concat("execute" +: name: _*)

    runSim(circuit, enableVcd = true) { tester =>
      for{
        op <- 0 until 3
        _ <- 0 to 1
      } {
        val operand = next(32)
        val shamt = next(5).toInt

        tester.poke(exec(NameTemplate.active), 1)
        tester.poke(exec("ops", NameTemplate.enumFlag), op)
        tester.poke(exec("operand"), operand)
        tester.poke(exec("shamt"), shamt)

        val mask = (BigInt(1) << 32) - 1
        val expect = op match {
          case 0 => (operand << shamt) & mask
          case 1 =>  operand >> shamt
          case 2 =>
            val tmp = operand >> shamt
            if((operand & (BigInt(1) << 31)) == 0) tmp
            else tmp | ((BigInt(1) << shamt) - 1) << (32 - shamt - 1)
        }

        val actual = tester.peek(exec(NameTemplate.ret))
        val message = s"ops: $op, operand: 0b${operand.toString(2)}, shamt: ${shamt} expect: 0b${expect.toString(2)}, actual: 0b${actual.toString(2)}"
        tester.step(1)
        tester.expect(exec(NameTemplate.ret), expect, message)
      }
    }
  }

  test("Decoder unit test") {
    val rnd = new Random(0)
    def next(width: Int): BigInt = BigInt(width, rnd)
    val circuit = untilThisPhase(Vector("riscv"), "Decoder", "Decoder.tchdl", "Types.tchdl")

    def truncate(v: BigInt, widthes: Int*): Seq[BigInt] = {
      val builder = Seq.newBuilder[BigInt]

      widthes.reverse.foldLeft(v) {
        case (remain, width) =>
          val mask = (1 << width) - 1
          builder += remain & mask
          remain >> width
      }

      builder.result()
    }

    def concat(bits: (Int, BigInt)*): BigInt = {
      val (_, res) = bits.reverse.foldLeft((0, BigInt(0))) {
        case ((offset, acc), (width, bits)) =>
          val res = acc | (bits << offset)
          (offset + width, res)
      }

      res
    }

    def luiInst(): { val inst: BigInt; val imm: BigInt; val rd: BigInt } = {
      val _imm = next(20)
      val _rd = next(5)
      val opcode = BigInt("0110111", 2)
      val _inst = _imm << 12 | _rd << 7 | opcode

      new {
        val inst = _inst
        val imm = _imm
        val rd = _rd
      }
    }

    def auipcInst(): { val inst: BigInt; val imm: BigInt; val rd: BigInt } = {
      val _imm = next(20)
      val _rd = next(5)
      val opcode = BigInt("0010111", 2)
      val _inst = _imm << 12 | _rd << 7 | opcode

      new {
        val inst = _inst
        val imm = _imm
        val rd = _rd
      }
    }

    def jalInst(): { val inst: BigInt; val imm: BigInt; val rd: BigInt } = {
      val immRaw = next(20)
      val _rd = next(5)
      val opcode = BigInt("1101111", 2)
      val Seq(bit20, bit10_1, bit11, bit19_12) = truncate(immRaw, 1, 10, 1, 8)
      val imm = concat((1, bit20), (8, bit19_12), (1, bit11), (10, bit10_1), (1, BigInt(0)))
      val _imm =
        if(bit20 == 1) BigInt("0xFFF00000", 16) | imm
        else imm
      val _inst = concat((20, immRaw), (5, _rd), (7, opcode))

      new {
        val inst = _inst
        val imm = _imm
        val rd = _rd
      }
    }

    def jalrInst(): { val inst: BigInt; val imm: BigInt; val rs1: BigInt; val rd: BigInt } = {
      val immRaw = next(12)
      val _rs1 = next(5)
      val _rd = next(5)
      val opcode = BigInt("1100111", 2)
      val _inst = immRaw << 20 | _rs1 << 15 | _rd << 7 | opcode
      val _imm =
        if((immRaw & (1 << 11)) == 0) immRaw
        else BigInt("0xFFFFF000", 16) | immRaw


      new {
        val inst = _inst
        val imm = _imm
        val rs1 = _rs1
        val rd = _rd
      }
    }

    runSim(circuit) { tester =>

    }
  }
}
