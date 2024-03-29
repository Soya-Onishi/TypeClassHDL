package tchdl

import tchdl.ast._
import tchdl.parser._
import tchdl.typecheck._
import tchdl.backend._
import tchdl.util._
import firrtl.{ir => fir}
import firrtl.stage.FirrtlCircuitAnnotation
import firrtl.transforms.{NoDCEAnnotation, SimplifyMems}
import firrtl.annotations.{Annotation, CircuitName, ComponentName, LoadMemoryAnnotation, MemoryLoadFileType, ModuleName}
import treadle.TreadleTester

import java.util.Random
import java.nio.file.{Files, Path, Paths}
import scala.collection.JavaConverters._
import org.scalatest.tags.Slow

@Slow
class RiscvTest extends TchdlFunSuite {
  def truncate(v: BigInt, widths: Int*): Seq[BigInt] = {
    val builder = Seq.newBuilder[BigInt]

    widths.reverse.foldLeft(v) {
      case (remain, width) =>
        val mask = (BigInt(1) << width) - 1
        builder += remain & mask
        remain >> width
    }

    builder.result()
  }

  def concat(bits: (Int, BigInt)*): BigInt = {
    val (_, res) = bits.reverse.foldLeft((0, BigInt(0))) {
      case ((offset, acc), (width, bits)) =>
        val mask = bits & ((BigInt(1) << width) - 1)
        val res = acc | ((bits & mask) << offset)
        (offset + width, res)
    }

    res
  }

  def signExt(bits: BigInt, msbIdx: Int, to: Int): BigInt = {
    val msb = bits & (BigInt(1) << msbIdx)
    if (msb == 0) bits
    else {
      val mask = ((BigInt(1) << to) - 1) ^ ((BigInt(1) << (msbIdx + 1)) - 1)
      bits | mask
    }
  }

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

  private def runSim(circuit: fir.Circuit, enableVcd: Boolean = false, createFile: Boolean = false, additionalAnnons: Seq[Annotation] = Seq.empty)(f: TreadleTester => Unit): Unit = {
    if (createFile) {
      val filename = s"${circuit.main}.fir"
      val path = Paths.get(s"./$filename")
      java.nio.file.Files.write(path, circuit.serialize.getBytes())
    }

    val clockInfo = treadle.executable.ClockInfo("CLK")
    val annons = Seq(
      treadle.ClockInfoAnnotation(Seq(clockInfo)),
      treadle.ResetNameAnnotation("RST"),
      FirrtlCircuitAnnotation(circuit),
    ) ++ additionalAnnons

    val passedAnnons =
      if (enableVcd) annons :+ treadle.WriteVcdAnnotation
      else annons

    val tester = TreadleTester(passedAnnons)

    f(tester)

    if (tester.finish) info(tester.reportString)
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

      for {
        port <- Seq("rs1_", "rs2_")
        idx <- 0 until 32
      } {
        tester.poke(port + "_active", 1)
        tester.poke(port + "addr", idx)

        val expect = if (idx == 0) BigInt(0) else seq(idx)
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

      for {
        (op, rawOp) <- ops.zipWithIndex
        _ <- 0 to 1000
      } {
        val a = next
        val b = next
        val v = (b << 32) | a

        tester.poke("execute__active", 1)
        tester.poke("execute_op__member", rawOp)
        tester.poke("execute_op__data", v)

        val expect = if (op(a, b)) 1 else 0
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

    def hazard(name: String, port: Int): String = NameTemplate.concat(s"isLoadHazardRs$port", name)

    def forward(stage: String, isSome: Boolean, rd: BigInt, data: BigInt, tester: TreadleTester): Unit = {
      val prefix = s"__$stage"
      val rdName = s"${prefix}Rd"
      val dataName = s"${prefix}Data"

      tester.poke(s"${rdName}_active", 1)
      tester.poke(s"${rdName}_bits__member", if (isSome) 1 else 0)
      tester.poke(s"${rdName}_bits__data", rd)
      tester.poke(s"${dataName}_active", 1)
      tester.poke(s"${dataName}_bits__member", if (isSome) 1 else 0)
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
      val data = if (addr == 0) BigInt(0) else next
      setRs(name, addr, data, tester)
      val expect =
        if (addr == 0) BigInt(0)
        else infos.filter(_._1)
          .find(_._2 == addr)
          .map { case (_, _, data) => data }
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
      tester.poke(hazard(NameTemplate.active, 1), 0)
      tester.poke(hazard(NameTemplate.active, 2), 0)

      for (_ <- 0 to 100000) {
        val execForward = rnd.nextBoolean()
        val memForward = rnd.nextBoolean()
        val wbForward = rnd.nextBoolean()
        val forwardFlags = Seq(execForward, memForward, wbForward)

        val tuples = (forwardFlags zip Seq("exec", "mem", "wb")).map {
          case (bool, name) =>
            val rd = next % 32
            val data = next

            if (bool) forward(name, isSome = true, rd, data, tester)
            else disable(name, tester)

            (rd, data)
        }

        val infos = (forwardFlags zip tuples).map { case (flag, (rd, data)) => (flag, rd, data) }
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
        tester.poke("__isExeLoad_bits", if (execLoad) 1 else 0)
        tester.poke("__isMemLoad_bits", if (memLoad) 1 else 0)
        tester.poke("__isLoadDone_bits", if (loadDone) 1 else 0)
        tester.poke("isLoadHazardRs1__active", 1)
        tester.poke("isLoadHazardRs2__active", 1)
        tester.poke("isLoadHazardRs1_addr", rs1Addr)
        tester.poke("isLoadHazardRs2_addr", rs2Addr)

        val exeHazardRs1 = infos(0)._1 && (infos(0)._2 == rs1Addr) && execLoad
        val memHazardRs1 = infos(1)._1 && (infos(1)._2 == rs1Addr) && memLoad && !loadDone
        val exeHazardRs2 = infos(0)._1 && (infos(0)._2 == rs2Addr) && execLoad
        val memHazardRs2 = infos(1)._1 && (infos(1)._2 == rs2Addr) && memLoad && !loadDone
        tester.expect("isLoadHazardRs1__ret", if (exeHazardRs1 | memHazardRs1) 1 else 0)
        tester.expect("isLoadHazardRs2__ret", if (exeHazardRs2 | memHazardRs2) 1 else 0)

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
      for {
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
          case 1 => operand >> shamt
          case 2 =>
            val tmp = operand >> shamt
            if ((operand & (BigInt(1) << 31)) == 0) tmp
            else tmp | ((BigInt(1) << shamt) - 1) << (32 - shamt - 1)
        }

        val actual = tester.peek(exec(NameTemplate.ret))
        val message = s"ops: $op, operand: 0b${operand.toString(2)}, shamt: ${shamt} expect: 0b${expect.toString(2)}, actual: 0b${actual.toString(2)}"
        tester.step(1)
        tester.expect(exec(NameTemplate.ret), expect, message)
      }
    }
  }

  def decoderTemplate(inst: BigInt, pc: BigInt, tester: TreadleTester, rnd: Random): (BigInt, BigInt) = {
    def next(width: Int): BigInt = BigInt(width, rnd)

    val regs = BigInt(0) +: Seq.fill(31)(next(32))

    tester.poke("decode__active", 1)
    tester.poke("decode_inst", inst)
    tester.poke("decode_pc", pc)

    val rs1Addr = tester.peek("regFile_rs1_addr").toInt
    val rs2Addr = tester.peek("regFile_rs2_addr").toInt
    val rs1Data = regs(rs1Addr)
    val rs2Data = regs(rs2Addr)
    tester.poke("regFile_rs1__ret", rs1Data)
    tester.poke("regFile_rs2__ret", rs2Data)
    tester.poke("fu_rs1__ret", rs1Data)
    tester.poke("fu_rs2__ret", rs2Data)

    (rs1Data, rs2Data)
  }

  test("Decoder for lui instruction unit test") {
    val rnd = new Random(0)
    def next(width: Int): BigInt = BigInt(width, rnd)

    val circuit = untilThisPhase(Vector("riscv"), "Decoder", "Decoder.tchdl", "ForwardingUnit.tchdl", "RegisterFile.tchdl", "Types.tchdl")

    def luiInst(): {val inst: BigInt; val imm: BigInt; val rd: BigInt} = {
      val _imm = next(20)
      val _rd = next(5)
      val opcode = BigInt("0110111", 2)
      val _inst = concat((20, _imm), (5, _rd), (7, opcode))

      new {
        val inst = _inst
        val imm = _imm << 12
        val rd = _rd
      }
    }

    runSim(circuit, enableVcd = true) { tester =>
      for (_ <- 0 to 100) {
        val inst = luiInst()
        val pc = next(32)
        decoderTemplate(inst.inst, pc, tester, rnd)

        tester.step(1)

        val bits = tester.peek("decode__ret_ops__data")
        val Seq(aluOps, imm, zero) = truncate(bits, 32, 32, 3)
        val expectBits = concat((32, BigInt(0)), (32, inst.imm), (3, BigInt(0)))
        tester.expect("decode__ret_ops__member", 0)
        val message =
          s"""
             |[all] expect: ${expectBits.toString(16)}, actual ${bits.toString(16)}
             |[ops] expect: 0, actual: $aluOps
             |[imm] expect: ${inst.imm.toString(16)}, actual: ${imm.toString(16)}
             |[zer] expect: 0, actual: $zero
             |""".stripMargin
        tester.expect("decode__ret_ops__data", expectBits, message)
        tester.expect("decode__ret_rs1__member", 0)
        tester.expect("decode__ret_rs2__member", 0)
        tester.expect("decode__ret_rd__member", 1)
        tester.expect("decode__ret_rd__data", inst.rd)
      }
    }
  }

  test("Decoder unit test for AUIPC") {
    val rnd = new Random(0)

    def next(width: Int): BigInt = BigInt(width, rnd)

    val circuit = untilThisPhase(Vector("riscv"), "Decoder", "Decoder.tchdl", "ForwardingUnit.tchdl", "RegisterFile.tchdl", "Types.tchdl")

    def auipcInst(): {val inst: BigInt; val imm: BigInt; val rd: BigInt} = {
      val immRaw = next(20)
      val _rd = next(5)
      val opcode = BigInt("0010111", 2)
      val _inst = concat((20, immRaw), (5, _rd), (7, opcode))
      val _imm = concat((20, immRaw), (12, BigInt(0)))

      new {
        val inst = _inst
        val imm = _imm
        val rd = _rd
      }
    }

    runSim(circuit, createFile = true) { tester =>
      for (_ <- 0 until 100) {
        val inst = auipcInst()
        val pc = next(32)

        decoderTemplate(inst.inst, pc, tester, rnd)
        tester.step(1)

        tester.expect("decode__ret_ops__member", 0)

        val bits = tester.peek("decode__ret_ops__data")
        val Seq(aluOps, pcValue, imm) = truncate(bits, 32, 32, 3)
        val expectBits = concat((32, inst.imm), (32, pc), (3, BigInt(0)))
        val message =
          s"""
             |[all] expect: ${expectBits.toString(16)}, actual ${bits.toString(16)}
             |[ops] expect: 0, actual: $aluOps
             |[imm] expect: ${inst.imm.toString(16)}, actual: ${imm.toString(16)}
             |[ pc] expect: ${pc.toString(16)}, actual: ${pcValue.toString(16)}
             |""".stripMargin
        tester.expect("decode__ret_ops__data", expectBits, message)
        tester.expect("decode__ret_rs1__member", 0)
        tester.expect("decode__ret_rs2__member", 0)
        tester.expect("decode__ret_rd__member", 1)
        tester.expect("decode__ret_rd__data", inst.rd)
      }
    }
  }

  test("Decoder unit test for JAL") {
    val rnd = new Random(0)
    def next(width: Int): BigInt = BigInt(width, rnd)
    val circuit = untilThisPhase(Vector("riscv"), "Decoder", "Decoder.tchdl", "ForwardingUnit.tchdl", "RegisterFile.tchdl", "Types.tchdl")

    def jalInst(): {val inst: BigInt; val imm: BigInt; val rd: BigInt} = {
      val immRaw = next(20)
      val _rd = next(5)
      val opcode = BigInt("1101111", 2)
      val Seq(bit19_12, bit11, bit10_1, bit20) = truncate(immRaw, 1, 10, 1, 8)
      val imm = concat((1, bit20), (8, bit19_12), (1, bit11), (10, bit10_1), (1, BigInt(0)))
      val _imm = signExt(imm, 20, 32)
      val _inst = concat((20, immRaw), (5, _rd), (7, opcode))

      new {
        val inst = _inst
        val imm = _imm
        val rd = _rd
      }
    }

    runSim(circuit, enableVcd = true, createFile = true) { tester =>
      for (_ <- 0 until 100) {
        val inst = jalInst()
        val pc = next(32)

        decoderTemplate(inst.inst, pc, tester, rnd)
        tester.step(1)

        tester.expect("decode__ret_ops__member", 3)
        val bits = tester.peek("decode__ret_ops__data")
        val Seq(jmpMember, _, pcValue, imm) = truncate(bits, 32, 32, 3 + 32 + 32, 2)
        val expectBits = concat((32, inst.imm), (32, pc), (67, BigInt(0)), (2, BigInt(1)))
        val message =
          s"""
             |[all] expect: ${expectBits.toString(16)}, actual ${bits.toString(16)}
             |[mem] expect: 1, actual: $jmpMember
             |[imm] expect: ${inst.imm.toString(16)}, actual: ${imm.toString(16)}
             |[ pc] expect: ${pc.toString(16)}, actual: ${pcValue.toString(16)}
             |""".stripMargin
        tester.expect("decode__ret_ops__data", expectBits, message)
        tester.expect("decode__ret_rs1__member", 0)
        tester.expect("decode__ret_rs2__member", 0)
        tester.expect("decode__ret_rd__member", 1)
        tester.expect("decode__ret_rd__data", inst.rd)
      }
    }
  }

  test("Decoder unit test for JALR") {
    val rnd = new Random(0)

    def next(width: Int): BigInt = BigInt(width, rnd)

    val circuit = untilThisPhase(Vector("riscv"), "Decoder", "Decoder.tchdl", "ForwardingUnit.tchdl", "RegisterFile.tchdl", "Types.tchdl")
    val regs = BigInt(0) +: Seq.fill(31)(next(32))

    def jalrInst(): {val inst: BigInt; val imm: BigInt; val rs1: BigInt; val rd: BigInt} = {
      val immRaw = next(12)
      val _rs1 = next(5)
      val _rd = next(5)
      val opcode = BigInt("1100111", 2)
      val _inst = concat((12, immRaw), (5, _rs1), (3, BigInt(0)), (5, _rd), (7, opcode))
      val _imm = signExt(immRaw, 11, 32)

      new {
        val inst = _inst
        val imm = _imm
        val rs1 = _rs1
        val rd = _rd
      }
    }

    runSim(circuit, enableVcd = true, additionalAnnons = Seq(NoDCEAnnotation)) { tester =>
      for (_ <- 0 until 100) {
        val inst = jalrInst()
        val pc = next(32)

        val (rs1Data, _) = decoderTemplate(inst.inst, pc, tester, rnd)
        tester.step(1)

        val bits = tester.peek("decode__ret_ops__data")
        val Seq(jmpMember, _, rs1, imm) = truncate(bits, 32, 32, 67, 2)
        val expectBits = concat((32, inst.imm), (32, rs1Data), (35, BigInt(0)), (32, pc), (2, BigInt(2)))
        val message =
          s"""
             |[all] expect: ${expectBits.toString(16)}, actual ${bits.toString(16)}
             |[mem] expect: 2, actual: $jmpMember
             |[imm] expect: ${inst.imm.toString(16)}, actual: ${imm.toString(16)}
             |[rs1] expect: ${rs1Data.toString(16)}, actual: ${rs1.toString(16)}
             |[ pc] expect: ${pc.toString(16)}, actual:
             |""".stripMargin
        tester.expect("decode__ret_ops__member", 3)
        tester.expect("decode__ret_ops__data", expectBits, message)
        tester.expect("decode__ret_rs1__member", 1)
        tester.expect("decode__ret_rs2__member", 0)
        tester.expect("decode__ret_rd__member", 1)
        tester.expect("decode__ret_rd__data", inst.rd)
      }
    }
  }

  test("Decoder unit test for BRANCH") {
    val rnd = new Random(0)

    def next(width: Int): BigInt = BigInt(width, rnd)

    val circuit = untilThisPhase(Vector("riscv"), "Decoder", "Decoder.tchdl", "ForwardingUnit.tchdl", "RegisterFile.tchdl", "Types.tchdl")

    def branchInst(f3: Int): {val inst: BigInt; val imm: BigInt; val rs1: BigInt; val rs2: BigInt} = {
      val immRaw0 = next(5)
      val immRaw1 = next(7)
      val Seq(bit11, bit4_1) = truncate(immRaw0, 4, 1)
      val Seq(bit10_5, bit12) = truncate(immRaw1, 1, 6)
      val opcode = BigInt("1100011", 2)
      val _rs1 = next(5)
      val _rs2 = next(5)
      val immRaw = concat((1, bit12), (1, bit11), (6, bit10_5), (4, bit4_1), (1, BigInt(0)))
      val _imm = signExt(immRaw, 12, 32)
      val _inst = concat((7, immRaw1), (5, _rs2), (5, _rs1), (3, BigInt(f3)), (5, immRaw0), (7, opcode))

      new {
        val inst = _inst
        val imm = _imm
        val rs1 = _rs1
        val rs2 = _rs2
      }
    }

    val branches = Seq(0 -> 0, 1 -> 1, 2 -> 4, 3 -> 5, 4 -> 6, 5 -> 7)
    val regs = BigInt(0) +: Seq.fill(31)(next(32))

    runSim(circuit) { tester =>
      for {
        (op, f3) <- branches
        _ <- 0 until 100
      } {
        val inst = branchInst(f3)
        val pc = next(32)

        val (rs1Data, rs2Data) = decoderTemplate(inst.inst, pc, tester, rnd)
        tester.step(1)

        val bits = tester.peek("decode__ret_ops__data")
        val Seq(jmpMember, jmpData, pcValue, imm) = truncate(bits, 32, 32, 32 + 32 + 3, 2)
        val Seq(cmpMember, rs1Value, rs2Value) = truncate(jmpData, 32, 32, 3)
        val expectCmp = concat((32, rs2Data), (32, rs1Data), (3, op))
        val expectBits = concat((32, inst.imm), (32, pc), (67, expectCmp), (2, BigInt(0)))
        val message =
          s"""
             |[jmpMem] expect: 0, actual: $jmpMember
             |[cmpMem] expect: $op, actual: $cmpMember
             |[   rs1] expect: ${rs1Data.toString(16)}, actual: ${rs1Value.toString(16)}
             |[   rs2] expect: ${rs2Data.toString(16)}, actual: ${rs2Value.toString(16)}
             |[    pc] expect: ${pc.toString(16)}, actual: ${pcValue.toString(16)}
             |[   imm] expect: ${inst.imm.toString(16)}, actual: ${imm.toString(16)}
             |""".stripMargin
        tester.expect("decode__ret_ops__member", 3)
        tester.expect("decode__ret_ops__data", expectBits, message)
        tester.expect("decode__ret_rs1__member", 1)
        tester.expect("decode__ret_rs2__member", 1)
        tester.expect("decode__ret_rd__member", 0)
        tester.expect("decode__ret_rs1__data", inst.rs1)
        tester.expect("decode__ret_rs2__data", inst.rs2)
      }
    }
  }

  test("Decoder unit test for LOAD") {
    val rnd = new Random(0)

    def next(width: Int): BigInt = BigInt(width, rnd)

    val circuit = untilThisPhase(Vector("riscv"), "Decoder", "Decoder.tchdl", "ForwardingUnit.tchdl", "RegisterFile.tchdl", "Types.tchdl")

    def load(f3: Int): {val inst: BigInt; val imm: BigInt; val rs1: BigInt; val rd: BigInt} = {
      val immRaw = next(12)
      val _rs1 = next(5)
      val _rd = next(5)
      val opcode = BigInt("0000011", 2)
      val _imm = signExt(immRaw, 11, 32)
      val _inst = concat((12, immRaw), (5, _rs1), (3, BigInt(f3)), (5, _rd), (7, opcode))

      new {
        val inst = _inst
        val imm = _imm
        val rs1 = _rs1
        val rd = _rd
      }
    }

    val regs = BigInt(0) +: Seq.fill(31)(next(32))
    val ops = Seq(0 -> 0, 1 -> 1, 2 -> 2, 3 -> 4, 4 -> 5)

    runSim(circuit) { tester =>
      for {
        (op, f3) <- ops
        _ <- 0 until 100
      } {
        val inst = load(f3)
        val pc = next(32)
        val (rs1Data, _) = decoderTemplate(inst.inst, pc, tester, rnd)
        tester.step(1)

        val bits = tester.peek("decode__ret_ops__data")
        val Seq(dataType, rs1, imm) = truncate(bits, 32, 32, 3)
        val expectBits = concat((32, inst.imm), (32, rs1Data), (3, BigInt(op)))
        val message =
          s"""
             |[data] expect $op, actual $dataType
             |[ rs1] expect ${rs1Data.toString(16)}, actual: ${rs1.toString(16)}
             |[ imm] expect ${inst.imm.toString(16)}, actual: ${imm.toString(16)}
             |""".stripMargin
        tester.expect("decode__ret_ops__member", 4)
        tester.expect("decode__ret_ops__data", expectBits, message)
        tester.expect("decode__ret_rs1__member", 1)
        tester.expect("decode__ret_rs1__data", inst.rs1)
        tester.expect("decode__ret_rs2__member", 0)
        tester.expect("decode__ret_rd__member", 1)
        tester.expect("decode__ret_rd__data", inst.rd)
      }
    }
  }

  test("Decoder unit test for STORE") {
    val rnd = new Random(0)

    def next(width: Int): BigInt = BigInt(width, rnd)

    val circuit = untilThisPhase(Vector("riscv"), "Decoder", "Decoder.tchdl", "ForwardingUnit.tchdl", "RegisterFile.tchdl", "Types.tchdl")

    def store(f3: Int): {val inst: BigInt; val imm: BigInt; val rs1: BigInt; val rs2: BigInt} = {
      val immRaw0 = next(5)
      val immRaw1 = next(7)
      val _rs1 = next(5)
      val _rs2 = next(5)
      val opcode = BigInt("0100011", 2)
      val _imm = signExt(concat((7, immRaw1), (5, immRaw0)), 11, 32)
      val _inst = concat((7, immRaw1), (5, _rs2), (5, _rs1), (3, BigInt(f3)), (5, immRaw0), (7, opcode))

      new {
        val inst = _inst
        val imm = _imm
        val rs1 = _rs1
        val rs2 = _rs2
      }
    }

    val regs = BigInt(0) +: Seq.fill(31)(next(32))
    val ops = Seq(0 -> 0, 1 -> 1, 2 -> 2)

    runSim(circuit) { tester =>
      for {
        (op, f3) <- ops
        _ <- 0 until 100
      } {
        val inst = store(f3)
        val pc = next(32)

        val (rs1Data, rs2Data) = decoderTemplate(inst.inst, pc, tester, rnd)
        tester.step(1)

        val bits = tester.peek("decode__ret_ops__data")
        val Seq(dataType, rs1, imm, rs2) = truncate(bits, 32, 32, 32, 3)
        val expectedBits = concat((32, rs2Data), (32, inst.imm), (32, rs1Data), (3, dataType))
        val message =
          s"""
             |[data] expect $op, actual $dataType
             |[ rs1] expect ${rs1Data.toString(16)}, actual: ${rs1.toString(16)}
             |[ imm] expect ${inst.imm.toString(16)}, actual: ${imm.toString(16)}
             |[  rd] expect ${rs2Data.toString(16)}, actual: ${rs2.toString(16)}
             |""".stripMargin
        tester.expect("decode__ret_ops__member", 5)
        tester.expect("decode__ret_ops__data", expectedBits, message)
        tester.expect("decode__ret_rs1__member", 1)
        tester.expect("decode__ret_rs2__member", 1)
        tester.expect("decode__ret_rd__member", 0)
        tester.expect("decode__ret_rs1__data", inst.rs1)
        tester.expect("decode__ret_rs2__data", inst.rs2)
      }
    }
  }

  test("Decoder unit test for Arithmetic with Immediate") {
    val rnd = new Random(0)

    def next(width: Int): BigInt = BigInt(width, rnd)

    val circuit = untilThisPhase(Vector("riscv"), "Decoder", "Decoder.tchdl", "ForwardingUnit.tchdl", "RegisterFile.tchdl", "Types.tchdl")

    val regs = BigInt(0) +: Seq.fill(31)(next(32))
    val ops = Seq(0 -> 0, 2 -> 7, 3 -> 6, 4 -> 4)

    def arithImm(f3: Int): {val inst: BigInt; val imm: BigInt; val rs1: BigInt; val rd: BigInt} = {
      val immRaw = next(12)
      val _rs1 = next(5)
      val _rd = next(5)
      val opcode = BigInt("0010011", 2)
      val _imm = signExt(immRaw, 11, 32)
      val _inst = concat((12, immRaw), (5, _rs1), (3, BigInt(f3)), (5, _rd), (7, opcode))

      new {
        val inst = _inst
        val imm = _imm
        val rs1 = _rs1
        val rd = _rd
      }
    }

    runSim(circuit) { tester =>
      for {
        (op, f3) <- ops
        _ <- 0 until 100
      } {
        val inst = arithImm(f3)
        val pc = next(32)

        val (rs1Data, _) = decoderTemplate(inst.inst, pc, tester, rnd)
        tester.step(1)

        val bits = tester.peek("decode__ret_ops__data")
        val expect = concat((32, inst.imm), (32, rs1Data), (3, BigInt(op)))
        val Seq(aluOps, rs1, imm) = truncate(bits, 32, 32, 3)
        val message =
          s"""
             |[ops] expect: $op, actual: $aluOps
             |[rs1] expect: ${rs1Data.toString(16)}, actual: ${rs1.toString(16)}
             |[imm] expect: ${inst.imm.toString(16)}, actual: ${imm.toString(16)}
             |""".stripMargin
        tester.expect("decode__ret_ops__member", 0)
        tester.expect("decode__ret_ops__data", expect, message)
        tester.expect("decode__ret_rs1__member", 1)
        tester.expect("decode__ret_rs2__member", 0)
        tester.expect("decode__ret_rd__member", 1)
        tester.expect("decode__ret_rs1__data", inst.rs1)
        tester.expect("decode__ret_rd__data", inst.rd)
      }
    }
  }

  test("Decoder unit test for Compare(SLTI and SLTIU) with Immediate") {
    val rnd = new Random(0)

    def next(width: Int): BigInt = BigInt(width, rnd)

    val circuit = untilThisPhase(Vector("riscv"), "Decoder", "Decoder.tchdl", "ForwardingUnit.tchdl", "RegisterFile.tchdl", "Types.tchdl")

    val regs = BigInt(0) +: Seq.fill(31)(next(32))
    val ops = Seq(2 -> 2, 4 -> 3)

    def arithImm(f3: Int): {val inst: BigInt; val imm: BigInt; val rs1: BigInt; val rd: BigInt} = {
      val immRaw = next(12)
      val _rs1 = next(5)
      val _rd = next(5)
      val opcode = BigInt("0010011", 2)
      val _imm = signExt(immRaw, 11, 32)
      val _inst = concat((12, immRaw), (5, _rs1), (3, BigInt(f3)), (5, _rd), (7, opcode))

      new {
        val inst = _inst
        val imm = _imm
        val rs1 = _rs1
        val rd = _rd
      }
    }

    runSim(circuit) { tester =>
      for {
        (op, f3) <- ops
        _ <- 0 until 100
      } {
        val inst = arithImm(f3)
        val pc = next(32)
        val (rs1Data, _) = decoderTemplate(inst.inst, pc, tester, rnd)
        tester.step(1)

        val bits = tester.peek("decode__ret_ops__data")
        val expect = concat((32, inst.imm), (32, rs1Data), (3, BigInt(op)))
        val Seq(cmpOps, rs1, imm) = truncate(bits, 32, 32, 3)
        val message =
          s"""
             |[ops] expect: $op, actual: $cmpOps
             |[rs1] expect: ${rs1Data.toString(16)}, actual: ${rs1.toString(16)}
             |[imm] expect: ${inst.imm.toString(16)}, actual: ${imm.toString(16)}
             |""".stripMargin
        tester.expect("decode__ret_ops__member", 2)
        tester.expect("decode__ret_ops__data", expect, message)
        tester.expect("decode__ret_rs1__member", 1)
        tester.expect("decode__ret_rs2__member", 0)
        tester.expect("decode__ret_rd__member", 1)
        tester.expect("decode__ret_rs1__data", inst.rs1)
        tester.expect("decode__ret_rd__data", inst.rd)
      }
    }
  }

  test("Decoder unit test for SHIFT with Immediate") {
    val rnd = new Random(0)
    def next(width: Int): BigInt = BigInt(width, rnd)
    val circuit = untilThisPhase(Vector("riscv"), "Decoder", "Decoder.tchdl", "ForwardingUnit.tchdl", "RegisterFile.tchdl", "Types.tchdl")

    def shiftImm(op: Int): {val inst: BigInt; val shamt: BigInt; val rs1: BigInt; val rd: BigInt} = {
      val _shamt = next(5)
      val _rs1 = next(5)
      val _rd = next(5)
      val opcode = BigInt("0010011", 2)

      val f7 = op match {
        case 0 => BigInt("0000000", 2)
        case 1 => BigInt("0000000", 2)
        case 2 => BigInt("0100000", 2)
      }
      val f3 = op match {
        case 0 => BigInt("001", 2)
        case 1 => BigInt("101", 2)
        case 2 => BigInt("101", 2)
      }

      val _inst = concat((7, f7), (5, _shamt), (5, _rs1), (3, f3), (5, _rd), (7, opcode))

      new {
        val inst = _inst
        val shamt = _shamt
        val rs1 = _rs1
        val rd = _rd
      }
    }

    val regs = BigInt(0) +: Seq.fill(31)(next(32))

    runSim(circuit) { tester =>
      for {
        op <- 0 to 2
        _ <- 0 until 100
      } {
        val inst = shiftImm(op)
        val pc = next(32)
        val (rs1Data, _) = decoderTemplate(inst.inst, pc, tester, rnd)
        tester.step(1)

        val bits = tester.peek("decode__ret_ops__data")
        val expect = concat((5, inst.shamt), (32, rs1Data), (2, BigInt(op)))
        val Seq(cmpOps, rs1, shamt) = truncate(bits, 5, 32, 2)
        val message =
          s"""
             |[  ops] expect: $op, actual: $cmpOps
             |[  rs1] expect: ${rs1Data.toString(16)}, actual: ${rs1.toString(16)}
             |[shamt] expect: ${inst.shamt}, actual: $shamt
             |""".stripMargin
        tester.expect("decode__ret_ops__member", 1)
        tester.expect("decode__ret_ops__data", expect, message)
        tester.expect("decode__ret_rs1__member", 1)
        tester.expect("decode__ret_rs2__member", 0)
        tester.expect("decode__ret_rd__member", 1)
        tester.expect("decode__ret_rs1__data", inst.rs1)
        tester.expect("decode__ret_rd__data", inst.rd)
      }
    }
  }

  test("Decoder unit test for Arithmetic with Register") {
    val rnd = new Random(0)
    def next(width: Int): BigInt = BigInt(width, rnd)
    val circuit = untilThisPhase(Vector("riscv"), "Decoder", "Decoder.tchdl", "ForwardingUnit.tchdl", "RegisterFile.tchdl", "Types.tchdl")

    def arithReg(f3: Int, f7: Int): {val inst: BigInt; val rs1: BigInt; val rs2: BigInt; val rd: BigInt} = {
      val _rs1 = next(5)
      val _rs2 = next(5)
      val _rd = next(5)
      val opcode = BigInt("0110011", 2)
      val _inst = concat((7, BigInt(f7)), (5, _rs2), (5, _rs1), (3, BigInt(f3)), (5, _rd), (7, opcode))

      new {
        val inst = _inst
        val rs1 = _rs1
        val rs2 = _rs2
        val rd = _rd
      }
    }

    val regs = BigInt(0) +: Seq.fill(31)(next(32))
    val ops = Seq((0, 0, BigInt("0000000", 2)), (1, 0, BigInt("0100000", 2)), (2, 7, BigInt("0000000", 2)), (3, 6, BigInt("0000000", 2)), (4, 4, BigInt("0000000", 2)))

    runSim(circuit) { tester =>
      for {
        (op, f3, f7) <- ops
        _ <- 0 until 100
      } {
        val inst = arithReg(f3, f7.toInt)
        val pc = next(32)
        val (rs1Data, rs2Data) = decoderTemplate(inst.inst, pc, tester, rnd)
        tester.step(1)

        val bits = tester.peek("decode__ret_ops__data")
        val expect = concat((32, rs2Data), (32, rs1Data), (3, BigInt(op)))
        val Seq(aluOps, rs1, rs2) = truncate(bits, 32, 32, 3)
        val message =
          s"""
             |[  ops] expect: $op, actual: $aluOps
             |[  rs1] expect: ${rs1Data.toString(16)}, actual: ${rs1.toString(16)}
             |[  rs2] expect: ${rs2Data.toString(16)}, actual: ${rs2.toString(16)}
             |""".stripMargin
        tester.expect("decode__ret_ops__member", 0)
        tester.expect("decode__ret_ops__data", expect, message)
        tester.expect("decode__ret_rs1__member", 1)
        tester.expect("decode__ret_rs2__member", 1)
        tester.expect("decode__ret_rd__member", 1)
        tester.expect("decode__ret_rs1__data", inst.rs1)
        tester.expect("decode__ret_rs2__data", inst.rs2)
        tester.expect("decode__ret_rd__data", inst.rd)
      }
    }
  }

  test("Decoder unit test for Shift with Register") {
    val rnd = new Random(0)
    def next(width: Int): BigInt = BigInt(width, rnd)
    val circuit = untilThisPhase(Vector("riscv"), "Decoder", "Decoder.tchdl", "ForwardingUnit.tchdl", "RegisterFile.tchdl", "Types.tchdl")

    def arithReg(f3: Int, f7: Int): {val inst: BigInt; val rs1: BigInt; val rs2: BigInt; val rd: BigInt} = {
      val _rs1 = next(5)
      val _rs2 = next(5)
      val _rd = next(5)
      val opcode = BigInt("0110011", 2)
      val _inst = concat((7, BigInt(f7)), (5, _rs2), (5, _rs1), (3, BigInt(f3)), (5, _rd), (7, opcode))

      new {
        val inst = _inst
        val rs1 = _rs1
        val rs2 = _rs2
        val rd = _rd
      }
    }

    val regs = BigInt(0) +: Seq.fill(31)(next(32))
    val ops = Seq((0, 1, BigInt("0000000", 2)), (1, 5, BigInt("0000000", 2)), (2, 5, BigInt("0100000", 2)))

    runSim(circuit) { tester =>
      for {
        (op, f3, f7) <- ops
        _ <- 0 until 100
      } {
        val inst = arithReg(f3, f7.toInt)
        val pc = next(32)
        val (rs1Data, rs2Data) = decoderTemplate(inst.inst, pc, tester, rnd)
        tester.step(1)

        val bits = tester.peek("decode__ret_ops__data")
        val expect = concat((5, rs2Data), (32, rs1Data), (2, BigInt(op)))
        val shamtValue = rs2Data & 0x1F
        val Seq(aluOps, rs1, shamt) = truncate(bits, 5, 32, 2)
        val message =
          s"""
             |[  ops] expect: $op, actual: $aluOps
             |[  rs1] expect: ${rs1Data.toString(16)}, actual: ${rs1.toString(16)}
             |[  rs2] expect: $shamtValue, actual: $shamt
             |""".stripMargin
        tester.expect("decode__ret_ops__member", 1)
        tester.expect("decode__ret_ops__data", expect, message)
        tester.expect("decode__ret_rs1__member", 1)
        tester.expect("decode__ret_rs2__member", 1)
        tester.expect("decode__ret_rd__member", 1)
        tester.expect("decode__ret_rs1__data", inst.rs1)
        tester.expect("decode__ret_rs2__data", inst.rs2)
        tester.expect("decode__ret_rd__data", inst.rd)
      }
    }
  }

  test("Decoder unit test for Compare with Register") {
    val rnd = new Random(0)
    def next(width: Int): BigInt = BigInt(width, rnd)
    val circuit = untilThisPhase(Vector("riscv"), "Decoder", "Decoder.tchdl", "ForwardingUnit.tchdl", "RegisterFile.tchdl", "Types.tchdl")

    def arithReg(f3: Int, f7: Int): {val inst: BigInt; val rs1: BigInt; val rs2: BigInt; val rd: BigInt} = {
      val _rs1 = next(5)
      val _rs2 = next(5)
      val _rd = next(5)
      val opcode = BigInt("0110011", 2)
      val _inst = concat((7, BigInt(f7)), (5, _rs2), (5, _rs1), (3, BigInt(f3)), (5, _rd), (7, opcode))

      new {
        val inst = _inst
        val rs1 = _rs1
        val rs2 = _rs2
        val rd = _rd
      }
    }

    val regs = BigInt(0) +: Seq.fill(31)(next(32))
    val ops = Seq((2, 2, BigInt("0000000", 2)), (4, 3, BigInt("0000000", 2)))

    runSim(circuit) { tester =>
      for {
        (op, f3, f7) <- ops
        _ <- 0 until 100
      } {
        val inst = arithReg(f3, f7.toInt)
        val pc = next(32)
        val (rs1Data, rs2Data) = decoderTemplate(inst.inst, pc, tester, rnd)
        tester.step(1)

        val bits = tester.peek("decode__ret_ops__data")
        val expect = concat((32, rs2Data), (32, rs1Data), (3, BigInt(op)))
        val Seq(cmpOps, rs2, rs1) = truncate(bits, 32, 32, 3)
        val message =
          s"""
             |[  ops] expect: $op, actual: $cmpOps
             |[  rs1] expect: ${rs1Data.toString(16)}, actual: ${rs1.toString(16)}
             |[  rs2] expect: ${rs2Data.toString(16)}, actual: ${rs2.toString(16)}
             |""".stripMargin
        tester.expect("decode__ret_ops__member", 2)
        tester.expect("decode__ret_ops__data", expect, message)
        tester.expect("decode__ret_rs1__member", 1)
        tester.expect("decode__ret_rs2__member", 1)
        tester.expect("decode__ret_rd__member", 1)
        tester.expect("decode__ret_rs1__data", inst.rs1)
        tester.expect("decode__ret_rs2__data", inst.rs2)
        tester.expect("decode__ret_rd__data", inst.rd)
      }
    }
  }

  test("ALU unit test for Arithmetic") {
    val rnd = new Random(0)
    def next(width: Int): BigInt = BigInt(width, rnd)
    val circuit = untilThisPhase(Vector("riscv"), "ALU", "ALU.tchdl", "BarrelShifter.tchdl", "Comparator.tchdl", "Types.tchdl")

    runSim(circuit, createFile = true) { tester =>
      for{
        op <- 0 to 4
        _ <- 0 until 1000
      } {
        val operand0 = next(32)
        val operand1 = next(32)
        val rd = BigInt(0)
        val operationBits = concat((5, rd), (32, operand1), (32, operand0), (3, op))

        tester.poke("execute__active", 1)
        tester.poke("execute_op__member", 0)
        tester.poke("execute_op__data", operationBits)

        val expect = op match {
          case 0 => truncate(operand0 + operand1, 32).head
          case 1 => truncate(operand0 - operand1, 32).head
          case 2 => operand0 & operand1
          case 3 => operand0 | operand1
          case 4 => operand0 ^ operand1
        }

        tester.expect("execute__ret", expect)
      }
    }
  }

  test("ALU unit test for Shift") {
    val rnd = new Random(0)
    def next(width: Int): BigInt = BigInt(width, rnd)
    val circuit = untilThisPhase(Vector("riscv"), "ALU", "ALU.tchdl", "BarrelShifter.tchdl", "Comparator.tchdl", "Types.tchdl")

    runSim(circuit, createFile = true) { tester =>
      for{
        op <- 0 to 2
        _ <- 0 until 1000
      } {
        val operand0 = next(32)
        val operand1 = next(32)
        val rd = BigInt(0)
        val operationBits = concat((5, rd), (5, operand1), (32, operand0), (2, op))

        tester.poke("execute__active", 1)
        tester.poke("execute_op__member", 1)
        tester.poke("execute_op__data", operationBits)

        val shamt = truncate(operand1, 5).head.toInt
        val expect = op match {
          case 0 => truncate(operand0 << shamt, 32).head
          case 1 => truncate(operand0 >> shamt, 32).head
          case 2 =>
            val tmp = truncate(operand0 >> shamt, 32).head
            val idx = 32 - shamt - 1
            signExt(tmp, idx, 32)
        }

        val message =
          s"""
             |    op: $op
             |   rs1: ${operand0.toString(16).reverse.padTo(8, '0').reverse}
             | shamt: $shamt
             |expect: ${expect.toString(16).reverse.padTo(8, '0').reverse}
             |actual: ${tester.peek("execute__ret").toString(16).reverse.padTo(8, '0').reverse}
             |""".stripMargin
        tester.expect("execute__ret", expect, message)
      }
    }
  }

  test("ALU unit test for Compare") {
    val rnd = new Random(0)
    def next(width: Int): BigInt = BigInt(width, rnd)
    val circuit = untilThisPhase(Vector("riscv"), "ALU", "ALU.tchdl", "BarrelShifter.tchdl", "Comparator.tchdl", "Types.tchdl")

    def lessThanSigned(a: BigInt, b: BigInt): Boolean = {
      val Seq(aRemain, aMsb) = truncate(a, 1, 31)
      val Seq(bRemain, bMsb) = truncate(b, 1, 31)
      val tmp0 = concat((1, BigInt(0)), (1, ~aMsb), (31, aRemain))
      val tmp1 = concat((1, BigInt(0)), (1, ~bMsb), (31, bRemain))
      val comp = tmp0 - tmp1

      val Seq(_, msb) = truncate(comp,  1, 32)
      msb == 1
    }

    runSim(circuit, createFile = true) { tester =>
      for{
        op <- 0 to 5
        _ <- 0 until 1000
      } {
        val operand0 = next(32)
        val operand1 = next(32)
        val rd = BigInt(0)
        val operationBits = concat((5, rd), (32, operand1), (32, operand0), (3, op))

        tester.poke("execute__active", 1)
        tester.poke("execute_op__member", 2)
        tester.poke("execute_op__data", operationBits)

        val bool = op match {
          case 0 => operand0 == operand1
          case 1 => operand0 != operand1
          case 2 => lessThanSigned(operand0, operand1)
          case 3 => lessThanSigned(operand1, operand0)
          case 4 => operand0  < operand1
          case 5 => operand0 >= operand1
        }
        val expect = if(bool) BigInt(1) else BigInt(0)

        val message =
          s"""
             |    op: $op
             |   rs1: ${operand0.toString(16).reverse.padTo(8, '0').reverse}
             |   rs2: ${operand1.toString(16).reverse.padTo(8, '0').reverse}
             |expect: $expect
             |actual: ${tester.peek("execute__ret").toString(16).reverse.padTo(8, '0').reverse}
             |""".stripMargin
        tester.expect("execute__ret", expect, message)
      }
    }
  }

  test("ALU unit test for Load") {
    val rnd = new Random(0)
    def next(width: Int): BigInt = BigInt(width, rnd)
    val circuit = untilThisPhase(Vector("riscv"), "ALU", "ALU.tchdl", "BarrelShifter.tchdl", "Comparator.tchdl", "Types.tchdl")

    runSim(circuit, createFile = true) { tester =>
      for{
        op <- 0 to 4
        _ <- 0 until 1000
      } {
        val addr = next(32)
        val offset = next(32)
        val rd = BigInt(0)
        val operationBits = concat((5, rd), (32, offset), (32, addr), (3, op))

        tester.poke("execute__active", 1)
        tester.poke("execute_op__member", 4)
        tester.poke("execute_op__data", operationBits)

        val expect = truncate(addr + offset, 32).head

        val message =
          s"""
             |    op: $op
             |   rs1: ${  addr.toString(16).reverse.padTo(8, '0').reverse}
             |   rs2: ${offset.toString(16).reverse.padTo(8, '0').reverse}
             |expect: $expect
             |actual: ${tester.peek("execute__ret").toString(16).reverse.padTo(8, '0').reverse}
             |""".stripMargin
        tester.expect("execute__ret", expect, message)
      }
    }
  }

  test("ALU unit test for Store") {
    val rnd = new Random(0)
    def next(width: Int): BigInt = BigInt(width, rnd)
    val circuit = untilThisPhase(Vector("riscv"), "ALU", "ALU.tchdl", "BarrelShifter.tchdl", "Comparator.tchdl", "Types.tchdl")

    runSim(circuit, createFile = true) { tester =>
      for{
        op <- 0 to 2
        _ <- 0 until 1000
      } {
        val addr = next(32)
        val offset = next(32)
        val storeData = next(32)
        val operationBits = concat((32, storeData), (32, offset), (32, addr), (3, op))

        tester.poke("execute__active", 1)
        tester.poke("execute_op__member", 5)
        tester.poke("execute_op__data", operationBits)

        val expect = truncate(addr + offset, 32).head

        val message =
          s"""
             |    op: $op
             |   rs1: ${  addr.toString(16).reverse.padTo(8, '0').reverse}
             |   rs2: ${offset.toString(16).reverse.padTo(8, '0').reverse}
             |expect: $expect
             |actual: ${tester.peek("execute__ret").toString(16).reverse.padTo(8, '0').reverse}
             |""".stripMargin
        tester.expect("execute__ret", expect, message)
      }
    }
  }

  test("MemoryControlUnit unit test") {
    val rnd = new Random(0)
    def next(width: Int): BigInt = BigInt(width, rnd)
    val circuit = untilThisPhase(Vector("riscv"), "MemoryControlUnit", "MemoryControlUnit.tchdl")
    var idleCount = 0

    runSim(circuit, enableVcd = true, createFile = true, additionalAnnons = Seq(NoDCEAnnotation)) { tester =>
      def idle(): Unit = {
        idleCount += 1
        if(idleCount >= 25) {
          tester.fail(1)
          fail()
        }
      }

      tester.poke("loadInst__active", 0)
      tester.poke("loadData__active", 0)
      tester.poke("storeData__active", 0)

      for(idx <- 0 until 256) {
        tester.poke("storeData__active", 1)
        tester.poke("storeData_addr", idx * 4)
        tester.poke("storeData_data", idx)
        tester.poke("storeData_mask", 0xF)
        while(tester.peek("storeData__ret") == 0) { tester.step(1) }
        tester.step(1)
        tester.poke("storeData__active", 0)
      }

      for(idx <- 0 until 256) {
        tester.poke("loadData__active", 1)
        tester.poke("loadData_addr", idx * 4)
        while(tester.peek("loadData__ret__member") == 0) { tester.step(1); idle() }
        idleCount = 0
        tester.step(1)
        tester.poke("loadData__active", 0)
        while(tester.peek("_pointer_1__member") == 0) { tester.step(1); idle() }
        idleCount = 0
        tester.expect("_pointer_1__data", idx)
        tester.step(1)
      }

      tester.poke("loadInst__active", 0)
      tester.poke("loadData__active", 0)
      tester.poke("storeData__active", 0)
      tester.step(10)

      val memBusy = tester.peek("memBusy") == 1
      val loadInstRunning = tester.peek("loadInstRunning") == 1
      val loadDataRunning = tester.peek("loadDataRunning") == 1

      while(memBusy | loadInstRunning | loadDataRunning) { tester.step(1); idle() }
      idleCount = 0

      tester.poke("loadInst__active", 1)
      tester.poke("loadInst_addr", 0)
      tester.poke("loadData__active", 1)
      tester.poke("loadData_addr", 0)

      tester.expect("loadInst__ret__member", 1)
      tester.expect("loadData__ret__member", 0)
      tester.step(1)

      tester.poke("loadInst__active", 0)
      tester.poke("loadData__active", 0)
      while(tester.peek("_pointer_0__member") == 0) {
        tester.poke("loadData__active", 1)
        tester.expect("loadData__ret__member", 0)
        tester.step(1)
      }
    }
  }

  test("build core") {
    val rnd = new Random(0)
    def next(width: Int): BigInt = BigInt(width, rnd)
    val circuit = untilThisPhase(
      Vector("riscv"), "Top",
      "Top.tchdl",
      "Core.tchdl",
      "MemoryControlUnit.tchdl",
      "RegisterFile.tchdl",
      "ForwardingUnit.tchdl",
      "Decoder.tchdl",
      "ALU.tchdl",
      "BarrelShifter.tchdl",
      "Comparator.tchdl",
      "CacheController.tchdl",
      "Cache.tchdl",
      "LRUController.tchdl",
      "Types.tchdl"
    )

    def doTest(files: Seq[Path]): Unit = {
      val file = files.head
      var testFail = false

      val annons = Seq(
        LoadMemoryAnnotation(ComponentName("memory", ModuleName("MemoryControlUnit_0", CircuitName("Top_0"))), file.toString, MemoryLoadFileType.Hex)
      )

      runSim(circuit, enableVcd = true, createFile = true,additionalAnnons = annons) { tester =>
        print(s"$file: ")
        var fail = false

        tester.step(10)
        tester.poke("launch__active", 1)
        tester.poke("launch_pc", 0)
        tester.step(1)
        tester.poke("launch__active", 0)

        try {
          while(tester.peek("reachTerminate__member") == 0) { tester.step(1) }
        } catch {
          case _: treadle.executable.StopException => tester.fail(1); fail = true
        }

        if(fail) println("err")
        else {
          val gp = tester.peek("reachTerminate__data")
          println(gp)
          fail = gp != 1
        }

        testFail = fail
      }

      if(testFail | files.tail.isEmpty) ()
      else doTest(files.tail)
    }

    doTest(Files.list(Paths.get("./hexs")).iterator().asScala.toSeq)
    // doTest(Seq(Paths.get("./hexs/rv32ui-p-simple.hex")))
  }

  test("compile Cache") {
    val circuit = untilThisPhase(Vector("riscv"), "Cache", "Cache.tchdl")
    runSim(circuit, createFile = true) { tester => }
  }
}
