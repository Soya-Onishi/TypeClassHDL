package tchdl.backend

import tchdl.backend.ast.{BackendLIR => lir}
import tchdl.util._

import firrtl.{ir => fir}
import scala.reflect.ClassTag
import scala.reflect.runtime.universe.TypeTag
import scala.collection.mutable

object FirrtlCodeGen {
  case class ElaboratedModule(name: String, path: Vector[String], module: fir.Module, subs: Vector[ElaboratedModule])

  val clockRef = fir.Reference("CLK", fir.ClockType)
  val resetRef = fir.Reference("RST", fir.UIntType(fir.IntWidth(1)))

  def exec(
    top: lir.Module,
    moduleList: Vector[lir.Module],
    pointers: Vector[PointerConnection],
  )(implicit global: GlobalData): fir.Circuit = {
    val suffixTable = mutable.Map.empty[String, Int]
    val moduleName = getNameWithSuffix(top.tpe)(suffixTable)
    val elaborated = elaborate(top, moduleName, moduleList)(global, pointers, Vector.empty, suffixTable)
    val connectionMap = pointers
      .map(createPointerDataRoute)
      .flatMap(_.toVector)
      .map { case (key, value) => ("Top" +: key).mkString("_") -> value }
      .foldLeft(Map.empty[String, Vector[DataRoute]]) {
        case (acc, map) => acc.get(map._1) match {
          case None => acc.updated(map._1, map._2)
          case Some(route) => acc.updated(map._1, (map._2 ++ route).distinct)
        }
      }

    val modules = addPointerConnection(elaborated, connectionMap)(global, pointers)
    fir.Circuit(fir.NoInfo, modules, moduleName)
  }

  def getNameWithSuffix(tpe: BackendType)(implicit moduleSuffix: mutable.Map[String, Int]): String = {
    val tpeName = tpe.symbol.toString
    val suffix = moduleSuffix.get(tpeName) match {
      case None => 0
      case Some(suffix) => suffix
    }
    moduleSuffix(tpeName) = suffix + 1

    NameTemplate.concat(tpeName, suffix.toString)
  }

  def elaborate(module: lir.Module, moduleName: String, moduleList: Vector[lir.Module])(implicit global: GlobalData, pointers: Vector[PointerConnection], modulePath: Vector[String], moduleSuffix: mutable.Map[String, Int]): ElaboratedModule = {
    val ports = module.ports.map(elaboratePort)
    val clkPort = fir.Port(fir.NoInfo, clockRef.name, fir.Input, fir.ClockType)
    val rstPort = fir.Port(fir.NoInfo, resetRef.name, fir.Input, fir.UIntType(fir.IntWidth(1)))

    val (mems, memInitss) = module.mems.map(elaborateMemory).unzip
    val components = module.components.flatMap(elaborateStmt)
    val inits = module.inits.flatMap(elaborateStmt)
    val procedures = module.procedures.flatMap(elaborateStmt)
    val priorityAssigns = findAllComponents[lir.PriorityAssign](module.procedures)
    val (viaWires, viaInitss, condAssigns) = priorityAssigns.map(elaboratePriorityAssignToDst).unzip3
    val viaInits = viaInitss.flatten

    val clkConnects = module.subs
      .map(sub => fir.Reference(sub.name, fir.UnknownType))
      .map(ref => fir.SubField(ref, clockRef.name, fir.UnknownType))
      .map(ref => fir.Connect(fir.NoInfo, ref, clockRef))
    val rstConnects = module.subs
      .map(sub => fir.Reference(sub.name, fir.UnknownType))
      .map(ref => fir.SubField(ref, resetRef.name, fir.UnknownType))
      .map(ref => fir.Connect(fir.NoInfo, ref, resetRef))

    val modulePorts = Vector(clkPort, rstPort) ++ ports
    val subModules = module.subs.map(sub => sub.name -> moduleList.find(_.tpe == sub.tpe).get)
    val subTuples = subModules.map{ case (name, sub) =>
      val modName = getNameWithSuffix(sub.tpe)
      val mod = elaborate(sub, modName, moduleList)(global, pointers, modulePath :+ name, moduleSuffix)

      (name, modName, mod)
    }
    val instances = subTuples.map { case (instanceName, modName, _) => fir.DefInstance(fir.NoInfo, instanceName, modName) }
    val subs = subTuples.map(_._3)
    val body = fir.Block(
        instances ++
        clkConnects ++
        rstConnects ++
        mems ++
        memInitss.flatten ++
        components ++
        viaWires ++
        inits ++
        viaInits ++
        procedures ++
        condAssigns
    )

    val elaboratedModule = fir.Module(fir.NoInfo, moduleName, modulePorts, body)

    ElaboratedModule(moduleName, modulePath, elaboratedModule, subs)
  }

  def elaboratePort(port: lir.Port)(implicit global: GlobalData, pointers: Vector[PointerConnection]): fir.Port = {
    val lir.Port(dir, name, tpe) = port
    val firrtlTpe = toFirrtlType(tpe)
    val direction = dir match {
      case lir.Dir.Input => fir.Input
      case lir.Dir.Output => fir.Output
    }

    fir.Port(fir.NoInfo, name, direction, firrtlTpe)
  }

  def elaborateSubModule(sub: lir.SubModule)(implicit moduleSuffix: mutable.Map[String, Int]): fir.DefInstance = {
    fir.DefInstance(fir.NoInfo, sub.name, getNameWithSuffix(sub.tpe))
  }

  def typeFlatten(tpe: fir.Type): fir.Type = tpe match {
    case tpe: fir.UIntType => tpe
    case fir.BundleType(fields) =>
      val width = fields.map(_.tpe).map(typeFlatten).foldLeft(BigInt(0)){
        case (acc, fir.UIntType(fir.IntWidth(width))) => acc + width
      }
      fir.UIntType(fir.IntWidth(width))
    case fir.VectorType(tpe, size) =>
      val fir.UIntType(fir.IntWidth(width)) = typeFlatten(tpe)
      fir.UIntType(fir.IntWidth(width * size))
  }

  def concatAllData(ref: fir.Expression, dataTpe: fir.Type): fir.Expression = dataTpe match {
    case _: fir.UIntType => ref
    case fir.BundleType(fields) =>
      fields.map(field => fir.SubField(ref, field.name, field.tpe)).reduceLeft[fir.Expression]{
        case (lsb, msb) =>
          val right = concatAllData(fir.SubField(ref, msb.name, msb.tpe), msb.tpe)
          val fir.UIntType(fir.IntWidth(leftWidth)) = lsb.tpe
          val fir.UIntType(fir.IntWidth(rightWidth)) = right.tpe
          val concatTpe = fir.UIntType(fir.IntWidth(leftWidth + rightWidth))

          fir.DoPrim(firrtl.PrimOps.Cat, Seq(right, lsb), Seq.empty, concatTpe)
      }
    case fir.VectorType(tpe, size) =>
      (0 until size).map{idx => fir.SubIndex(ref, idx, tpe) }.reduceLeft[fir.Expression] {
        case (lsb, msb) =>
          val right = concatAllData(msb, msb.tpe)
          val fir.UIntType(fir.IntWidth(accWidth)) = lsb.tpe
          val fir.UIntType(fir.IntWidth(rightWidth)) = right.tpe
          val concatTpe = fir.UIntType(fir.IntWidth(accWidth + rightWidth))

          fir.DoPrim(firrtl.PrimOps.Cat, Seq(right, lsb), Seq.empty, concatTpe)
      }
  }

  def elaborateMemory(mem: lir.Memory)(implicit global: GlobalData, pointers: Vector[PointerConnection], modulePath: Vector[String]): (fir.DefMemory, Vector[fir.Statement]) = {
    def memEnDelaysInit(port: Int, tpe: fir.Type): Vector[fir.Statement] = {
      val template = NameTemplate.memEnDelay(mem.name, port)
      val wireName = s"${template}_init"
      val wire = fir.DefWire(fir.NoInfo, wireName, tpe)
      val initConnects = (0 until mem.readLatency).map { idx =>
        fir.Connect(
          fir.NoInfo,
          fir.SubIndex(fir.Reference(wireName, fir.UnknownType), idx, fir.UnknownType),
          fir.UIntLiteral(0)
        )
      }

      wire +: initConnects.toVector
    }

    def createDelayWire: Vector[fir.Statement] = {
      val wires = (0 until mem.readPorts).toVector
        .map(idx => fir.DefWire(
          fir.NoInfo,
          NameTemplate.memEnDelay(mem.name, idx),
          fir.VectorType(fir.UIntType(fir.IntWidth(1)), 1)
        ))
      val inits = wires.map(wire => fir.Connect(
        fir.NoInfo,
        fir.SubIndex(fir.Reference(wire.name, fir.UnknownType), 0, fir.UnknownType),
        fir.UIntLiteral(0)
      ))

      wires ++ inits
    }

    def createDelayReg: Vector[fir.Statement] = {
      val memEnDelaysTpe = fir.VectorType(fir.UIntType(fir.IntWidth(1)), mem.readLatency)
      val memEnDelaysInits = (0 until mem.readPorts).toVector.flatMap(memEnDelaysInit(_, memEnDelaysTpe))
      val memEnDelays = (0 until mem.readPorts).toVector
        .map { idx =>
          fir.DefRegister(
            fir.NoInfo,
            NameTemplate.memEnDelay(mem.name, idx),
            memEnDelaysTpe,
            clockRef,
            resetRef,
            fir.Reference(s"${NameTemplate.memEnDelay(mem.name, idx)}_init", fir.UnknownType)
          )
        }

      val delaysConnections = (0 until mem.readPorts).flatMap { portIdx =>
        var connections = Vector.newBuilder[fir.Connect]
        val name = NameTemplate.memEnDelay(mem.name, portIdx)

        (0 until mem.readLatency).foldLeft[fir.Expression](fir.UIntLiteral(0)) {
          case (expr, idx) =>
            val refer = fir.SubIndex(fir.Reference(name, fir.UnknownType), idx, fir.UnknownType)
            connections += fir.Connect(fir.NoInfo, refer, expr)
            refer
        }

        connections.result()
      }

      memEnDelaysInits ++ memEnDelays ++ delaysConnections.toVector
    }

    def getPointerWire(port: Int): fir.Reference = {
      val candidates = pointers.filter(_.source.modulePath == modulePath)
      val pointer = candidates.find(_.source.component == HierarchyComponent.Memory(mem.name, port)).get
      val name = NameTemplate.pointerWire(pointer.id)
      val tpe = fir.BundleType(Seq(
        fir.Field(NameTemplate.enumFlag, fir.Default, fir.UIntType(fir.IntWidth(1))),
        fir.Field(NameTemplate.enumData, fir.Default, toFirrtlType(mem.dataTpe))
      ))

      fir.Reference(name, tpe)
    }

    def createReadDataConnections(port: Int): Vector[fir.Statement] = {
      val member = fir.SubField(getPointerWire(port), NameTemplate.enumFlag, fir.UIntType(fir.IntWidth(1)))
      val data = fir.SubField(getPointerWire(port), NameTemplate.enumData, toFirrtlType(mem.dataTpe))
      val delayRef = fir.Reference(NameTemplate.memEnDelay(mem.name, port), fir.UnknownType)
      val memRef = fir.Reference(mem.name, fir.UnknownType)
      val portRef = fir.SubField(memRef, s"r$port", fir.UnknownType)
      val memDataRef = fir.SubField(portRef, "data", typeFlatten(toFirrtlType(mem.dataTpe)))
      val referIndex = if (mem.readLatency == 0) 0 else mem.readLatency - 1
      val connectMember = fir.Connect(fir.NoInfo, member, fir.SubIndex(delayRef, referIndex, fir.UnknownType))
      val connectData = fir.Connect(fir.NoInfo, data, memDataRef)

      Vector(connectMember, connectData)
    }

    val readers = (0 until mem.readPorts).map(id => "r" + id)
    val writers = (0 until mem.writePorts).map(id => "w" + id)

    val readPortInvalids = readers.flatMap { reader =>
      val memRef = fir.Reference(mem.name, fir.UnknownType)
      val ref = fir.SubField(memRef, reader, fir.UnknownType)
      val addr = fir.SubField(ref, "addr", fir.UnknownType)
      val en = fir.SubField(ref, "en", fir.UIntType(fir.IntWidth(1)))
      val clk = fir.SubField(ref, "clk", fir.ClockType)
      val clkConnect = fir.Connect(fir.NoInfo, clk, clockRef)

      Vector(fir.IsInvalid(fir.NoInfo, addr), fir.Connect(fir.NoInfo, en, fir.UIntLiteral(0)), clkConnect)
    }

    val writePortInvalids = writers.flatMap{ writer =>
      def maskHierarchy(tpe: BackendType): fir.Type = {
        if(tpe.fields.isEmpty) fir.UIntType(fir.IntWidth(1))
        else {
          val fields = tpe.fields.map { case (name, t) => fir.Field(name, fir.Default, maskHierarchy(t)) }.toSeq
          val sortedFields = fields.sortWith{ case (l, r) => l.name < r.name }
          fir.BundleType(sortedFields)
        }
      }

      def maskAllOne(tpe: fir.Type, ref: fir.Expression): Vector[fir.Connect] = {
        tpe match {
          case fir.BundleType(fields) =>
            fields.flatMap{ field => maskAllOne(field.tpe, fir.SubField(ref, field.name, field.tpe)) }.toVector
          case fir.UIntType(_) =>
            Vector(fir.Connect(fir.NoInfo, ref, fir.UIntLiteral(1)))
        }
      }

      val memRef = fir.Reference(mem.name, fir.UnknownType)
      val ref = fir.SubField(memRef, writer, fir.UnknownType)
      val addr = fir.SubField(ref, "addr", fir.UnknownType)
      val data = fir.SubField(ref, "data", fir.UnknownType)
      val en = fir.SubField(ref, "en", fir.UIntType(fir.IntWidth(1)))
      val clk = fir.SubField(ref, "clk", fir.ClockType)
      val maskType = maskHierarchy(mem.dataTpe)
      val maskDefaultName = s"${mem.name}_${writer}_mask"
      val maskDefaultRef = fir.Reference(maskDefaultName, maskType)
      val maskDefaultConnects = maskAllOne(maskType, maskDefaultRef)
      val mask = fir.SubField(ref, "mask", fir.UIntType(fir.IntWidth(1)))

      val otherStmts = Vector(
        fir.IsInvalid(fir.NoInfo, addr),
        fir.IsInvalid(fir.NoInfo, data),
        fir.Connect(fir.NoInfo, en, fir.UIntLiteral(0)),
        fir.Connect(fir.NoInfo, clk, clockRef),
        fir.Connect(fir.NoInfo, mask, fir.UIntLiteral(1))
      )

      fir.DefWire(fir.NoInfo, maskDefaultName, maskType) +: (maskDefaultConnects ++ otherStmts)
    }

    val delayStmts =
      if (mem.readLatency == 0) createDelayWire
      else createDelayReg

    val readDataConnections = (0 until mem.readPorts).flatMap(createReadDataConnections)

    val memory = fir.DefMemory(
      fir.NoInfo,
      mem.name,
      typeFlatten(toFirrtlType(mem.dataTpe)),
      mem.size,
      mem.writeLatency,
      mem.readLatency,
      readers,
      writers,
      Seq.empty,
      fir.ReadUnderWrite.New
    )

    (memory, readPortInvalids.toVector ++ writePortInvalids.toVector ++ delayStmts ++ readDataConnections)
  }

  def elaboratePriorityAssignToDst(assign: lir.PriorityAssign)(implicit global: GlobalData, pointer: Vector[PointerConnection], modulePath: Vector[String]): (fir.DefWire, Vector[fir.Statement], fir.Conditionally) = {
    val dataTpe = toFirrtlType(assign.src.tpe)
    val enTpe = fir.UIntType(fir.IntWidth(1))
    val enField = fir.Field(NameTemplate.priorityEnable, fir.Default, enTpe)
    val dataField = fir.Field(NameTemplate.priorityData, fir.Default, dataTpe)

    // generate wire for via
    val viaTpe = fir.BundleType(Seq(enField, dataField))
    val viaWire = fir.DefWire(fir.NoInfo, assign.via, viaTpe)

    // generate initialization code for wire
    val viaRef = fir.Reference(assign.via, fir.UnknownType)
    val enRef = fir.SubField(viaRef, NameTemplate.priorityEnable, fir.UnknownType)
    val dataRef = fir.SubField(viaRef, NameTemplate.priorityData, fir.UnknownType)
    val defaultEn = fir.Connect(fir.NoInfo, enRef, fir.UIntLiteral(0))
    val invalidData = fir.IsInvalid(fir.NoInfo, dataRef)

    // generate code to assign to destination from via wire
    val dstRef = elaborateExpr(assign.dst)
    val assignDst = fir.Connect(fir.NoInfo, dstRef, dataRef)
    val cond = fir.Conditionally(fir.NoInfo, enRef, assignDst, fir.EmptyStmt)

    (viaWire, Vector(defaultEn, invalidData), cond)
  }

  def calculateWidth(tpe: fir.Type): BigInt = {
    tpe match {
      case fir.UIntType(fir.IntWidth(width)) => width
      case fir.BundleType(fields) => fields.map(_.tpe).map(calculateWidth).foldLeft(BigInt(0))(_ + _)
      case fir.VectorType(tpe, size) => calculateWidth(tpe) * size
    }
  }

  def elaborateStmt(stmt: lir.Stmt)(implicit global: GlobalData, pointer: Vector[PointerConnection], modulePath: Vector[String]): Vector[fir.Statement] =
    stmt match {
      case lir.Wire(name, tpe) =>
        val wireTpe = toFirrtlType(tpe)
        val width = calculateWidth(wireTpe)

        if(width == 0) Vector.empty
        else Vector(fir.DefWire(fir.NoInfo, name, wireTpe))
      case lir.Node(name, expr, tpe) =>
        val src = elaborateExpr(expr)
        val width = calculateWidth(src.tpe)

        if(width == 0) Vector.empty
        else Vector(fir.DefNode(fir.NoInfo, name, src))
      case lir.Reg(name, default, tpe) =>
        Vector(fir.DefRegister(
          fir.NoInfo,
          name,
          toFirrtlType(tpe),
          clockRef,
          resetRef,
          default.map(elaborateExpr).getOrElse(fir.Reference(name, toFirrtlType(tpe)))
        ))
      case lir.IDReg(proc, blk, name) =>
        val init = getPointer[HierarchyComponent.Proc](pointer, modulePath, proc.name.get, blk) match {
          case None => fir.Reference(name, idTpe)
          case Some(p) => fir.UIntLiteral(p.id, idWidth)
        }

        val reg = fir.DefRegister(fir.NoInfo, name, idTpe, clockRef, resetRef, init)
        Vector(reg)
      case lir.Assign(dst, src) =>
        val srcTpe = toFirrtlType(src.tpe)
        val width = calculateWidth(srcTpe)
        val connect = fir.Connect(fir.NoInfo, elaborateExpr(dst), elaborateExpr(src))

        if(width == 0) Vector.empty
        else Vector(connect)
      case lir.PriorityAssign(_, via, src) =>
        val viaRef = fir.Reference(via, fir.UnknownType)
        val subEn = fir.SubField(viaRef, "_enable", fir.UnknownType)
        val subData = fir.SubField(viaRef, "_data", fir.UnknownType)

        val enable = fir.Connect(fir.NoInfo, subEn, fir.UIntLiteral(1))
        val transfer = fir.Connect(fir.NoInfo, subData, elaborateExpr(src))

        Vector(enable, transfer)
      case lir.PartialAssign(dst, src) =>
        Vector(fir.PartialConnect(
          fir.NoInfo,
          elaborateExpr(dst),
          elaborateExpr(src)
        ))
      case lir.Invalid(ref) =>
        val r = elaborateExpr(ref)
        val width = calculateWidth(r.tpe)

        if(width == 0) Vector.empty
        else Vector(fir.IsInvalid(fir.NoInfo, r))
      case lir.When(cond, conseq, alt) =>
        Vector(fir.Conditionally(
          fir.NoInfo,
          elaborateExpr(cond),
          fir.Block(conseq.flatMap(elaborateStmt)),
          fir.Block(alt.flatMap(elaborateStmt))
        ))
      case pass: lir.PassID =>
        val idWidth = atLeastLength(pointer.length).toInt
        val idTpe = fir.UIntType(fir.IntWidth(idWidth))
        val dstRef = fir.Reference(pass.dst, idTpe)
        val srcRef = fir.Reference(pass.from, idTpe)
        val connect = fir.Connect(fir.NoInfo, dstRef, srcRef)

        Vector(connect)
      case ret: lir.Return => elaborateReturn(ret)
      case deref: lir.Deref => elaborateDeref(deref)
      case read: lir.MemRead => elaborateMemRead(read)
      case write: lir.MemWrite => elaborateMemWrite(write)
      case lir.Stop(msg) =>
        Vector(
          fir.Print(fir.NoInfo, fir.StringLit(msg), Seq.empty, clockRef, fir.UIntLiteral(1)),
          fir.Stop(fir.NoInfo, 1, clockRef, fir.UIntLiteral(1))
        )
    }

  def elaborateMemRead(memRead: lir.MemRead)(implicit global: GlobalData, pointer: Vector[PointerConnection], modulePath: Vector[String]): Vector[fir.Statement] = {
    val memRef = fir.Reference(memRead.name, fir.UnknownType)

    val portPath = fir.SubField(memRef, "r" + memRead.port, fir.UnknownType)
    val addrPath = fir.SubField(portPath, "addr", fir.UnknownType)
    val enablePath = fir.SubField(portPath, "en", fir.UnknownType)
    val enDelayPath = fir.SubIndex(
      fir.Reference(
        NameTemplate.memEnDelay(memRead.name, memRead.port),
        fir.UnknownType
      ),
      0,
      fir.UnknownType
    )

    val assignAddr = fir.Connect(fir.NoInfo, addrPath, elaborateExpr(memRead.addr))
    val assignEnable = fir.Connect(fir.NoInfo, enablePath, fir.UIntLiteral(1))
    val assignEnDelay = fir.Connect(fir.NoInfo, enDelayPath, fir.UIntLiteral(1))

    Vector(assignAddr, assignEnable, assignEnDelay)
  }

  def elaborateMemWrite(memWrite: lir.MemWrite)(implicit global: GlobalData, pointer: Vector[PointerConnection], modulePath: Vector[String]): Vector[fir.Statement] = {
    val memRef = fir.Reference(memWrite.name, fir.UnknownType)
    val portPath = fir.SubField(memRef, "w" + memWrite.port, fir.UnknownType)
    val addrPath = fir.SubField(portPath, "addr", fir.UnknownType)
    val dataPath = fir.SubField(portPath, "data", fir.UnknownType)
    val enablePath = fir.SubField(portPath, "en", fir.UnknownType)

    val assignAddr = fir.Connect(fir.NoInfo, addrPath, elaborateExpr(memWrite.addr))
    val assignEnable = fir.Connect(fir.NoInfo, enablePath, fir.UIntLiteral(1))
    val dataExpr = elaborateExpr(memWrite.data)
    val concatData = concatAllData(dataExpr, toFirrtlType(memWrite.data.tpe))
    val assignData = fir.Connect(fir.NoInfo, dataPath, concatData)

    Vector(assignAddr, assignEnable, assignData)
  }

  def elaborateReturn(ret: lir.Return)(implicit global: GlobalData, pointers: Vector[PointerConnection], modulePath: Vector[String]): Vector[fir.Statement] = {
    val exprRef = elaborateExpr(ret.expr)
    val modulePointers = pointers.filter(_.source.modulePath == modulePath)
    val procName = ret.path.name.get
    val procPointers = modulePointers.filter(_.source.component.isInstanceOf[HierarchyComponent.Proc])
    val dstPointers = procPointers.filter(_.source.component.asInstanceOf[HierarchyComponent.Proc].name == procName)
    val wireRefs = dstPointers.map(p => fir.Reference(NameTemplate.pointerWire(p.id), fir.UnknownType))

    ret.idName match {
      case None =>
        val connects = wireRefs.map(w => fir.Connect(fir.NoInfo, w, exprRef))
        connects
      case Some(name) =>
        val bitWidth = atLeastLength(pointers.length).toInt
        val width = fir.IntWidth(bitWidth)
        val tpe = fir.UIntType(width)
        val op0 = fir.Reference(name, tpe)

        val whens = (dstPointers.map(_.id) zip wireRefs).map {
          case (id, wire) =>
            val pointerRef = fir.Reference(NameTemplate.pointerWire(id), wire.tpe)
            val op1 = fir.UIntLiteral(id, width)

            fir.Conditionally(
              fir.NoInfo,
              fir.DoPrim(firrtl.PrimOps.Eq, Seq(op0, op1), Seq.empty, fir.UnknownType),
              fir.Connect(fir.NoInfo, pointerRef, exprRef),
              fir.EmptyStmt
            )
        }

        whens
    }
  }

  def elaborateExpr(expr: lir.Expr)(implicit global: GlobalData, pointers: Vector[PointerConnection], modulePath: Vector[String]): fir.Expression = expr match {
    case lir.Reference(name, tpe) => fir.Reference(name, toFirrtlType(tpe))
    case lir.SubField(ref, name, tpe) => fir.SubField(elaborateExpr(ref), name, toFirrtlType(tpe))
    case lir.SubIndex(ref, idx, tpe) => fir.SubIndex(elaborateExpr(ref), idx, toFirrtlType(tpe))
    case lir.SubAccess(ref, idx, tpe) =>
      fir.SubAccess(
        elaborateExpr(ref),
        elaborateExpr(idx),
        toFirrtlType(tpe)
      )
    case lir.Literal(value, tpe) =>
      val firTpe = toFirrtlType(tpe)
      val fir.UIntType(width) = firTpe

      fir.UIntLiteral(value, width)
    case commence: lir.Commence => elaborateCommence(commence)
    case lir.MemPortID(memName, portNumber, tpe) =>
      val width = toFirrtlType(tpe).asInstanceOf[fir.UIntType].width
      pointers.filter(_.source.modulePath == modulePath)
        .collect{ case PointerConnection(id, source, _, _) => id -> source }
        .collect{ case (id, HWHierarchyPath(_, HierarchyComponent.Memory(name, port))) => (id, name, port) }
        .collect{ case (id, name, port) if name == memName && port == portNumber => id }
        .map(id => fir.UIntLiteral(id, width))
        .head
    case lir.ProcStepID(procName, stepName, tpe) =>
      val width = toFirrtlType(tpe).asInstanceOf[fir.UIntType].width
      pointers.filter(_.source.modulePath == modulePath)
        .collect{ case PointerConnection(id, source, _, _) => id -> source }
        .collect{ case (id, HWHierarchyPath(_, HierarchyComponent.Proc(proc, step))) => (id, proc, step) }
        .collect{ case (id, proc, step) if proc == procName && step == stepName => id }
        .map(id => fir.UIntLiteral(id, width))
        .head
    case lir.Ops(op, args, consts, tpe) => fir.DoPrim(op, args.map(elaborateExpr), consts, toFirrtlType(tpe))
    case lir.Concat(subjects, tpe) =>
      val refs = subjects.map(elaborateExpr).filter(e => calculateWidth(e.tpe) != 0)
      val cats = refs.tail.foldLeft(refs.head) {
        case (prefix, next) => fir.DoPrim(firrtl.PrimOps.Cat, Seq(next, prefix), Seq.empty, fir.UnknownType)
      }

      cats match {
        case doPrim: fir.DoPrim => doPrim.copy(tpe = toFirrtlType(tpe))
        case expr => expr
      }
    case lir.Extract(target, history, tpe) =>
      def getWidth(tpe: BackendType): BigInt =
        toFirrtlType(tpe)
          .asInstanceOf[fir.UIntType].width
          .asInstanceOf[fir.IntWidth].width

      val from = history.tail.foldLeft(BigInt(0)) { case (idx, tpe) => idx + getWidth(tpe) }
      val to = from + getWidth(history.head) - 1

      val targetRef = elaborateExpr(target)
      fir.DoPrim(firrtl.PrimOps.Bits, Seq(targetRef), Seq(to, from), toFirrtlType(tpe))
  }

  def elaborateCommence(commence: lir.Commence)(implicit global: GlobalData, pointers: Vector[PointerConnection], modulePath: Vector[String]): fir.Expression = {
    val candidates = pointers.filter { pointer =>
      val isSameModule = pointer.source.modulePath == modulePath
      val isProc = pointer.source.component.isInstanceOf[HierarchyComponent.Proc]
      lazy val procComponent = pointer.source.component.asInstanceOf[HierarchyComponent.Proc]
      lazy val isSameName = procComponent.name == commence.path.name.get
      lazy val isSameBlock = procComponent.origin == commence.origin

      isSameModule && isProc && isSameName && isSameBlock
    }

    assert(candidates.length == 1)
    val pointer = candidates.head
    val idWidth = atLeastLength(pointers.length).toInt
    fir.UIntLiteral(pointer.id, fir.IntWidth(idWidth))
  }

  def elaborateDeref(deref: lir.Deref)(implicit global: GlobalData, pointers: Vector[PointerConnection], modulePath: Vector[String]): Vector[fir.Statement] = {
    def isNeeded(dst: HWHierarchyPath): Boolean = {
      val isSamePath = dst.modulePath == modulePath
      val isSameRef = dst.component == HierarchyComponent.Deref(deref.ref)

      isSamePath && isSameRef
    }

    val candidates = pointers.filter(_.dest.exists(isNeeded))
    val head = fir.Reference(NameTemplate.pointerWire(candidates.head.id), toFirrtlType(candidates.head.tpe))
    val muxResult = candidates.tail.foldLeft[fir.Expression](head) {
      case (alt, c) =>
        val pointerRef = elaborateExpr(deref.ref)
        val dataRef = fir.Reference(NameTemplate.pointerWire(c.id), toFirrtlType(c.tpe))
        val idLit = fir.UIntLiteral(c.id, fir.IntWidth(atLeastLength(candidates.length).toInt))
        val eq = fir.DoPrim(firrtl.PrimOps.Eq, Seq(pointerRef, idLit), Seq.empty, fir.UnknownType)

        fir.Mux(eq, dataRef, alt)
    }

    Vector(fir.DefNode(fir.NoInfo, deref.name, muxResult))
  }


  private def atLeastLength(x: Double): Double = {
    def log2(x: Double): Double = math.log10(x) / math.log10(2.0)

    val width = (math.ceil _ compose log2) (x)
    if (width == 0) 1
    else width
  }

  trait Connection
  object Connection {
    case object FromHere extends Connection
    case object FromParent extends Connection
    case class FromChild(sub: String) extends Connection {
      override def hashCode() = sub.hashCode
    }
    case class ToChild(sub: String) extends Connection {
      override def hashCode() = sub.hashCode
    }
    case object ToParent extends Connection
  }
  case class DataRoute(path: Vector[String], connects: Connection, id: Int, tpe: BackendType)


  private def createPointerDataRoute(pointer: PointerConnection): Map[Vector[String], Vector[DataRoute]] = {
    def sameUntil(path0: Vector[String], path1: Vector[String]): Int = {
      (path0.headOption, path1.headOption) match {
        case (Some(head0), Some(head1)) if head0 == head1 => sameUntil(path0.tail, path1.tail) + 1
        case _ => -1
      }
    }

    // create routes from parent module to child module
    def intoChild(from: Vector[String], to: Vector[String], tpe: BackendType): Vector[DataRoute] = {
      // `idx` is used to attach next child name to from's path
      def loop(from: Vector[String], to: Vector[String], idx: Int): Vector[DataRoute] = {
        val connect = DataRoute(from, Connection.FromParent, pointer.id, tpe)
        val anotherConnect =
          if (from == to) None
          else Some(DataRoute(from, Connection.ToChild(to(idx)), pointer.id, tpe))

        val route = connect +: anotherConnect.toVector

        if (from == to) route
        else route ++ loop(from :+ to(idx), to, idx + 1)
      }

      // At first, no need for connection from parent
      // because connection pattern is only two patterns like below
      // 1:
      //          --- * --- proc(starting point)
      //        /
      //   from                  <-
      //        \                <- subject to connect in this method
      //          --- * --- to   <-
      //
      // 2:
      //   from(also proc) --- * --- to
      val head =
      if (from == to) Vector.empty
      else Vector(DataRoute(from, Connection.ToChild(to.head), pointer.id, tpe))

      if (from == to) head
      else {
        val idx = sameUntil(from, to) + 1
        val nextFrom = from :+ to(idx)

        head ++ loop(nextFrom, to, idx + 1)
      }
    }

    def uptoParent(from: Vector[String], to: Vector[String], toOuter: Boolean, tpe: BackendType): Vector[DataRoute] = {
      def loop(from: Vector[String], to: Vector[String], child: String): Vector[DataRoute] = {
        val connection = DataRoute(from, Connection.FromChild(child), pointer.id, tpe)
        val another =
          if (from == to) None
          else Some(DataRoute(from, Connection.ToParent, pointer.id, tpe))

        val route = connection +: another.toVector

        if (from == to) route
        else route ++ loop(from.init, to, from.last)
      }

      val connection =
        if (from == to && !toOuter) Vector.empty
        else Vector(DataRoute(from, Connection.ToParent, pointer.id, tpe))

      if (from == to) connection
      else connection ++ loop(from.init, to, from.last)
    }

    def createRoute(source: HWHierarchyPath, dest: HWHierarchyPath, tpe: BackendType): Vector[DataRoute] = {
      val toOuterTopModule = dest.component.isInstanceOf[HierarchyComponent.TopRet]

      sameUntil(source.modulePath, dest.modulePath) match {
        case -1 =>
          uptoParent(source.modulePath, Vector.empty, toOuterTopModule, tpe) ++ intoChild(Vector.empty, dest.modulePath, tpe)
        case idx if source.modulePath.length == idx + 1 =>
          intoChild(source.modulePath, dest.modulePath, tpe)
        case idx if dest.modulePath.length == idx + 1 =>
          uptoParent(source.modulePath, dest.modulePath, toOuterTopModule, tpe)
        case idx =>
          val turnPoint = source.modulePath.take(idx + 1)
          uptoParent(source.modulePath, turnPoint, toOuterTopModule, tpe) ++ intoChild(turnPoint, dest.modulePath, tpe)
      }
    }

    val sourceRoute = DataRoute(pointer.source.modulePath, Connection.FromHere, pointer.id, pointer.tpe)
    val routes = pointer.dest
      .flatMap(createRoute(pointer.source, _, pointer.tpe))
      .distinct

    (routes :+ sourceRoute).groupBy(_.path)
  }

  def addPointerConnection(circuit: ElaboratedModule, map: Map[String, Vector[DataRoute]])(implicit global: GlobalData, pointers: Vector[PointerConnection]): Vector[fir.Module] = {
    val modulePath = "Top" +: circuit.path
    val key = modulePath.mkString("_")
    val newModule = map.get(key) match {
      case None => circuit.module
      case Some(routes) =>
        val (ports, stmts) = generateRoute(routes)
        val newPorts = circuit.module.ports ++ ports
        val oldBody = circuit.module.body.asInstanceOf[fir.Block]
        val (instances, others) = oldBody.stmts.collectPartition{ case inst: fir.DefInstance => inst }
        val newBody = fir.Block(instances ++ stmts ++ others)

        circuit.module.copy(ports = newPorts, body = newBody)
    }

    val subModules = circuit.subs.flatMap(addPointerConnection(_, map))
    newModule +: subModules
  }

  def generateRoute(routes: Vector[DataRoute])(implicit global: GlobalData, pointers: Vector[PointerConnection]): (Vector[fir.Port], Vector[fir.Statement]) = {
    def refChildPort(id: Int, sub: String, tpe: BackendType): fir.SubField =
      fir.SubField(
        fir.Reference(sub, fir.UnknownType),
        NameTemplate.pointerPort(id),
        toFirrtlType(tpe)
      )

    def refWire(id: Int, tpe: BackendType): fir.Reference =
      fir.Reference(
        NameTemplate.pointerWire(id),
        toFirrtlType(tpe)
      )

    def refPort(id: Int, tpe: BackendType): fir.Reference =
      fir.Reference(
        NameTemplate.pointerPort(id),
        toFirrtlType(tpe)
      )

    val wires = routes
      .map(route => (route.id, route.tpe))
      .distinct
      .map { case (id, tpe) =>
        fir.DefWire(
          fir.NoInfo,
          NameTemplate.pointerWire(id),
          toFirrtlType(tpe)
        )
      }

    val components = routes
      .filter(_.connects != Connection.FromHere)
      .map { route =>
        route.connects match {
          case Connection.FromChild(sub) =>
            val from = refChildPort(route.id, sub, route.tpe)
            val to = refWire(route.id, route.tpe)

            (Option.empty[fir.Port], fir.Connect(fir.NoInfo, to, from))
          case Connection.ToChild(sub) =>
            val from = refWire(route.id, route.tpe)
            val to = refChildPort(route.id, sub, route.tpe)

            (Option.empty[fir.Port], fir.Connect(fir.NoInfo, to, from))
          case Connection.ToParent =>
            val from = refWire(route.id, route.tpe)
            val to = refPort(route.id, route.tpe)
            val port = fir.Port(
              fir.NoInfo,
              NameTemplate.pointerPort(route.id),
              fir.Output,
              toFirrtlType(route.tpe)
            )

            (Some(port), fir.Connect(fir.NoInfo, to, from))
          case Connection.FromParent =>
            val from = refPort(route.id, route.tpe)
            val to = refWire(route.id, route.tpe)
            val port = fir.Port(
              fir.NoInfo,
              NameTemplate.pointerPort(route.id),
              fir.Input,
              toFirrtlType(route.tpe)
            )

            (Some(port), fir.Connect(fir.NoInfo, to, from))
        }
      }

    val (portOpts, stmts) = components.unzip
    val ports = portOpts.flatten

    (ports, wires ++ stmts)
  }

  private def getPointer[T <: HierarchyComponent : TypeTag : ClassTag](pointers: Vector[PointerConnection], modulePath: Vector[String], proc: String, blk: String): Option[PointerConnection] = {
    val pointer = pointers.filter { pointer =>
      val isSameModule = pointer.source.modulePath == modulePath
      val isProc = pointer.source.component.isInstanceOf[HierarchyComponent.Proc]
      lazy val procComponent = pointer.source.component.asInstanceOf[HierarchyComponent.Proc]
      lazy val isSameName = procComponent.name == proc
      lazy val isSameBlock = procComponent.origin == blk

      isSameModule && isProc && isSameName && isSameBlock
    }

    pointer match {
      case Vector(p) => Some(p)
      case _ => None
    }
  }

  private def idWidth(implicit pointers: Vector[PointerConnection]): fir.IntWidth = {
    val width = atLeastLength(pointers.length).toInt
    fir.IntWidth(width)
  }

  private def idTpe(implicit pointers: Vector[PointerConnection]): fir.UIntType = {
    fir.UIntType(idWidth)
  }

  private def findAllComponents[T <: lir.Stmt : TypeTag : ClassTag](stmts: Vector[lir.Stmt]): Vector[T] = {
    if(stmts.isEmpty) Vector.empty
    else {
      val components = stmts.collect{ case t: T => t }
      val whens = stmts.collect{ case w: lir.When => w }
      val conseqs = whens.flatMap(_.conseq)
      val alts = whens.flatMap(_.alt)

      components ++ findAllComponents(conseqs) ++ findAllComponents(alts)
    }
  }
}
