package tchdl

import tchdl.{ast => frontend}
import tchdl.util._
import tchdl.util.TchdlException.ImplementationErrorException

import scala.collection.immutable.ListMap
import firrtl.ir
import tchdl.ast.Position

package object backend {
  case class BuiltModule(tpe: BackendType, impl: Vector[ImplementClassContainer], noNeedElaborate: Boolean) {
    override def hashCode(): Int = tpe.hashCode + impl.hashCode + noNeedElaborate.hashCode()
  }

  trait ToFirrtlString {
    def toFirrtlString: String
  }

  sealed trait HPElem extends ToFirrtlString
  object HPElem {
    case class Num(n: Int) extends HPElem {
      override def hashCode(): Int = this.n.hashCode
      override def toString: String = this.n.toString
      override def toFirrtlString: String = this.toString
    }

    case class Str(s: String) extends HPElem {
      override def hashCode(): Int = this.s.hashCode
      override def toString: String = this.s
      override def toFirrtlString: String = this.toString
    }
  }

  class BackendTypeFlag(flagSeed: Int) {
    val flag = 1 << flagSeed

    def |(other: BackendTypeFlag): BackendTypeFlag = {
      val newFlag = this.flag | other.flag
      new BackendTypeFlag(0) {
        override val flag = newFlag
      }
    }

    def &(other: BackendTypeFlag): BackendTypeFlag = {
      val newFlag = this.flag & other.flag
      new BackendTypeFlag(0) {
        override val flag = newFlag
      }
    }

    def hasFlag(flag: BackendTypeFlag): Boolean = {
      val result = this & flag
      result.flag == flag.flag
    }

    override def equals(obj: Any): Boolean = obj match {
      case that: BackendTypeFlag => this.flag == that.flag
      case _ => false
    }

    override def hashCode(): Int = this.flag
  }
  object BackendTypeFlag {
    case object NoFlag extends BackendTypeFlag(0)
    case object Pointer extends BackendTypeFlag(1)
    case object EnumData extends BackendTypeFlag(2)
    case object EnumFlag extends BackendTypeFlag(3)
    case object DefaultInput extends BackendTypeFlag(4)
  }
  case class BackendType(flag: BackendTypeFlag, symbol: Symbol.TypeSymbol, hargs: Vector[HPElem], targs: Vector[BackendType]) extends ToFirrtlString {
    override def hashCode(): Int = symbol.hashCode + hargs.hashCode + targs.hashCode
    override def equals(obj: Any): Boolean = obj match {
      case that: BackendType =>
        this.symbol == that.symbol &&
        this.hargs == that.hargs &&
        this.targs == that.targs
      case _ => false
    }

    override def toString: String = {
      val pointer = if(flag.hasFlag(BackendTypeFlag.Pointer)) "&" else ""
      val head = symbol.name
      val args = hargs.map(_.toString) ++ targs.map(_.toString)
      val dataOf = if(flag.hasFlag(BackendTypeFlag.EnumData)) "Data of " else ""
      val flagOf = if(flag.hasFlag(BackendTypeFlag.EnumFlag)) "Flag of " else ""

      args match {
        case Vector() => s"$pointer$dataOf$flagOf$head"
        case args => s"$pointer$dataOf$flagOf$head[${args.mkString(",")}]"
      }
    }

    override lazy val toFirrtlString: String = {
      val head = {
        val pkg = this.symbol.path.pkgName.mkString("_")
        val name = this.symbol.path.name.get

        s"${pkg}_$name"
      }

      val args = {
        val hargs = this.hargs.map(_.toString)
        val targs = this.targs.map(_.toFirrtlString)

        val hargStr =
          if(hargs.isEmpty) ""
          else "__" + hargs.mkString("_")

        val targStr =
          if(targs.isEmpty) ""
          else "__" + targs.mkString("_")

        hargStr + targStr
      }

      head + args
    }

    def isHardware(implicit global: GlobalData): Boolean = {
      def verifyEnum(symbol: Symbol.EnumSymbol, verified: BackendType, types: Set[BackendType]): Boolean = {
        val memberFieldTypes = symbol.tpe.declares.toMap
          .values.toVector
          .map(_.tpe.asEnumMemberType)
          .flatMap(_.fields)
          .map(_.tpe.asRefType)

        val hpTable = (symbol.hps zip verified.hargs).toMap
        val tpTable = (symbol.tps zip verified.targs).toMap

        memberFieldTypes
          .map(toBackendType(_, hpTable, tpTable))
          .forall(loop(_, types + verified))
      }

      def loop(verified: BackendType, types: Set[BackendType]): Boolean = {
        verified.symbol match {
          case bit if bit == Symbol.bit => true
          case int if int == Symbol.int => true
          case bool if bool == Symbol.bool => true
          case string if string == Symbol.string => false
          case symbol: Symbol.EnumSymbol => verifyEnum(symbol, verified, types)
          case _ if global.lookupFields(verified).isEmpty => false
          case _ if types(verified) => false
          case _ => global.lookupFields(verified).values.forall(loop(_, types + verified))
        }
      }

      loop(this, Set.empty)
    }

    def fields(implicit global: GlobalData): Map[String, BackendType] = {
      val hpTable = (this.symbol.hps zip this.hargs).toMap
      val tpTable = (this.symbol.tps zip this.targs).toMap

      this.symbol match {
        case _: Symbol.EnumSymbol => Map.empty
        case symbol =>
          symbol.tpe.declares.toMap.map {
            case (name, symbol) =>
              name -> toBackendType(symbol.tpe.asRefType, hpTable, tpTable)
          }
      }
    }
  }

  object BackendType {
    def bitTpe(width: Int)(implicit global: GlobalData) = toBackendType(Type.bitTpe(width))
    def intTpe(implicit global: GlobalData) = BackendType(BackendTypeFlag.NoFlag, Symbol.int, Vector.empty, Vector.empty)
    def boolTpe(implicit global: GlobalData) = BackendType(BackendTypeFlag.NoFlag, Symbol.bool, Vector.empty, Vector.empty)
    def unitTpe(implicit global: GlobalData) = BackendType(BackendTypeFlag.NoFlag, Symbol.unit, Vector.empty, Vector.empty)
  }

  def toBackendType(tpe: Type.RefType)(implicit global: GlobalData): BackendType = toBackendType(tpe, Map.empty, Map.empty)
  def toBackendType(
    tpe: Type.RefType,
    hpTable: Map[Symbol.HardwareParamSymbol, HPElem],
    tpTable: Map[Symbol.TypeParamSymbol, BackendType]
  )(implicit global: GlobalData): BackendType = {
    def replace(tpe: Type.RefType): BackendType = tpe.origin match {
      case tp: Symbol.TypeParamSymbol =>
        tpTable.getOrElse(tp, throw new ImplementationErrorException(s"$tp should be found in tpTable"))
      case _: Symbol.EntityTypeSymbol =>
        val hargs = tpe.hardwareParam.map(evalHPExpr(_, hpTable))
        val targs = tpe.typeParam.map(replace)
        val flag =
          if(tpe.isPointer) BackendTypeFlag.Pointer
          else BackendTypeFlag.NoFlag

        BackendType(flag, tpe.origin, hargs, targs)
      case symbol: Symbol.FieldTypeSymbol =>
        val accessor = tpe.accessor.getOrElse(throw new ImplementationErrorException(s"$symbol should have accessor"))
        val accessorTPTable = tpTable.map { case (tp, tpe) => tp -> toRefType(tpe)}
        val accessorHPTable = hpTable.map{
          case (hp, HPElem.Num(value)) => hp -> frontend.IntLiteral(value, Position.empty)
          case (hp, HPElem.Str(value)) => hp -> frontend.StringLiteral(value, Position.empty)
        }
        val replaced = accessor.replaceWithMap(accessorHPTable, accessorTPTable)

        val fieldTpe = replaced.lookupType(tpe.origin.name)(Position.empty)
          .toOption
          .getOrElse(throw new ImplementationErrorException(s"type ${tpe.origin.name} should be found"))
          .tpe
          .asRefType

        val cast = replaced.castedAs.getOrElse(throw new ImplementationErrorException(s"type $replaced should have castedAs field"))
        val interface = cast.origin.asInterfaceSymbol

        val interfaceHPTable = (interface.hps zip cast.hardwareParam).map{
          case (hparam, frontend.IntLiteral(value)) => hparam -> HPElem.Num(value)
          case (hparam, frontend.StringLiteral(value)) => hparam -> HPElem.Str(value)
          case (_, tree) => throw new ImplementationErrorException(s"[$tree] must not appear at hardware expression")
        }.toMap

        val interfaceTPTable = (interface.tps zip cast.typeParam)
          .map { case (tparam, targ) => tparam -> replace(targ) }
          .toMap

        toBackendType(fieldTpe, interfaceHPTable, interfaceTPTable)
    }

    replace(tpe)
  }

  def toRefType(sig: BackendType): Type.RefType = {
    def intoLiteral(elem: HPElem): frontend.HPExpr = elem match {
      case HPElem.Num(value) => frontend.IntLiteral(value, Position.empty)
      case HPElem.Str(value) => frontend.StringLiteral(value, Position.empty)
    }

    val hargs = sig.hargs.map(intoLiteral)
    val targs = sig.targs.map(toRefType)
    val isPointer = sig.flag.hasFlag(BackendTypeFlag.Pointer)
    if(sig.flag.hasFlag(BackendTypeFlag.EnumData) | sig.flag.hasFlag(BackendTypeFlag.EnumFlag))
      throw new ImplementationErrorException("converting into RefType for enum data or enum member does not support")

    Type.RefType(sig.symbol, hargs, targs, isPointer)
  }

  def toFirrtlType(tpe: BackendType)(implicit global: GlobalData, pointers: Vector[PointerConnection]): ir.Type = {
    def toBitType(width: Int): ir.UIntType = ir.UIntType(ir.IntWidth(width))
    def toVecType(length: Int, tpe: ir.Type): ir.VectorType = ir.VectorType(tpe, length)
    def toEnumType(symbol: Symbol.EnumSymbol): ir.Type = {
      def log2(x: Double): Double = math.log10(x) / math.log10(2.0)
      def flagWidth(x: BigInt): Int = math.ceil(log2(x.toDouble + 1)).toInt

      def makeBitLength(
        member: Type.EnumMemberType,
        hpTable: Map[Symbol.HardwareParamSymbol, HPElem],
        tpTable: Map[Symbol.TypeParamSymbol, BackendType]
      ): BigInt = {
        def loop(tpe: ir.Type): BigInt = tpe match {
          case ir.BundleType(fields) => fields.map(_.tpe).map(loop).sum
          case ir.VectorType(tpe, size) => loop(tpe) * size
          case ir.UIntType(ir.IntWidth(width)) => width
        }

        val fieldTypes = member.fields
          .map(_.tpe.asRefType)
          .map(toBackendType(_, hpTable, tpTable))
          .map(toFirrtlType)

        fieldTypes.map(loop).sum
      }

      val members = symbol.tpe.declares
        .toMap
        .toVector
        .map{ case (_, symbol) => symbol.asEnumMemberSymbol }
      val maxID = members.map(_.memberID).max

      val hpTable = (symbol.hps zip tpe.hargs).toMap
      val tpTable = (symbol.tps zip tpe.targs).toMap
      val memberTpe = ir.UIntType(ir.IntWidth(flagWidth(maxID)))
      val maxLength = members
        .map(_.tpe.asEnumMemberType)
        .map(makeBitLength(_, hpTable, tpTable))
        .max
      val dataTpe = ir.UIntType(ir.IntWidth(maxLength))

      if(tpe.flag.hasFlag(BackendTypeFlag.EnumData)) dataTpe
      else if(tpe.flag.hasFlag(BackendTypeFlag.EnumFlag)) memberTpe
      else {
        val member = ir.Field("_member", ir.Default, memberTpe)
        val data = ir.Field("_data", ir.Default, dataTpe)

        val field =
          if(maxLength == 0) Seq(member)
          else Seq(member, data)

        ir.BundleType(field)
      }
    }

    def toOtherType: ir.BundleType = {
      val typeFields = global.lookupFields(tpe)

      val fields = typeFields.map{ case (name, tpe) => name -> toFirrtlType(tpe) }
        .toVector
        .sortWith{ case ((left, _), (right, _)) => left < right }
        .map{ case (name, tpe) => ir.Field(name, ir.Default, tpe) }

      ir.BundleType(fields)
    }

    def pointerType: ir.Type = {
      def log2(x: Double): Double = math.log10(x) / math.log10(2.0)
      def atLeastLength(x: Double): Double = {
        val width = (math.ceil _ compose log2) (x)

        if (width == 0) 1
        else if(x == 0) 0
        else width
      }

      val width = atLeastLength(pointers.length).toInt
      ir.UIntType(ir.IntWidth(width))
    }

    if(tpe.flag.hasFlag(BackendTypeFlag.Pointer)) pointerType
    else {
      val baseTpe = tpe.symbol match {
        case symbol if symbol == Symbol.int  => toBitType(width = 32)
        case symbol if symbol == Symbol.bool => toBitType(width = 1)
        case symbol if symbol == Symbol.unit => toBitType(width = 0)
        case symbol if symbol == Symbol.bit =>
          val HPElem.Num(width) = tpe.hargs.head
          toBitType(width)
        case symbol if symbol.isModuleTypeSymbol => ir.UnknownType
        case symbol if symbol == Symbol.vec =>
          val HPElem.Num(length) = tpe.hargs.head
          val elemType = toFirrtlType(tpe.targs.head)

          toVecType(length, elemType)
        case symbol: Symbol.EnumSymbol => toEnumType(symbol)
        case _ => toOtherType
      }

      if(tpe.flag.hasFlag(BackendTypeFlag.DefaultInput)) {
        ir.BundleType(Seq(
          ir.Field(  NameTemplate.portBits, ir.Default, baseTpe),
          ir.Field(NameTemplate.portActive, ir.Default, ir.UIntType(ir.IntWidth(1)))
        ))
      } else baseTpe
    }
  }

  def evalHPExpr(hpExpr: frontend.HPExpr, hpTable: Map[Symbol.HardwareParamSymbol, HPElem]): HPElem =
    hpExpr match {
      case ident: frontend.Ident => hpTable.getOrElse(ident.symbol.asHardwareParamSymbol, throw new ImplementationErrorException("hardware parameter must be found"))
      case frontend.IntLiteral(value) => HPElem.Num(value)
      case frontend.StringLiteral(value) => HPElem.Str(value)
      case frontend.HPBinOp(left, right) =>
        val HPElem.Num(leftValue) = evalHPExpr(left, hpTable)
        val HPElem.Num(rightValue) = evalHPExpr(right, hpTable)
        HPElem.Num(leftValue + rightValue)
      case frontend.HPUnaryOp(ident) =>
        val HPElem.Num(value) = evalHPExpr(ident, hpTable)
        HPElem.Num(-value)
      case frontend.BoolLiteral(_) => throw new ImplementationErrorException("boolean literal must not appear at hardware expression")
    }

  def calculateFieldLength(tpe: BackendType)(implicit global: GlobalData): BigInt = {
    assert(!tpe.isHardware, s"calculated type must be hardware type but [${tpe.symbol}] is other kind of types")

    val bit = global.builtin.types.lookup("Bit")

    tpe.symbol match {
      case symbol if symbol == bit =>
        val HPElem.Num(width) = tpe.hargs.head
        BigInt(width)
      case enum: Symbol.EnumSymbol =>
        val hpTable = (enum.hps zip tpe.hargs).toMap
        val tpTable = (enum.tps zip tpe.targs).toMap

        enum.tpe.declares.toMap
          .values
          .map { _.asInstanceOf[Symbol.EnumMemberSymbol].tpe }
          .map {
            _.declares.toMap.values.view
              .map(_.tpe.asRefType)
              .map(toBackendType(_, hpTable, tpTable))
              .map(calculateFieldLength)
              .sum
          }
          .max
      case symbol =>
        val hpTable = (symbol.hps zip tpe.hargs).toMap
        val tpTable = (symbol.tps zip tpe.targs).toMap

        symbol.tpe.declares.toMap.values.view
          .map(_.tpe.asRefType)
          .map(toBackendType(_, hpTable, tpTable))
          .map(calculateFieldLength)
          .sum
    }
  }

  def findImplClassTree(impl: Symbol.ImplementSymbol, global: GlobalData): Option[frontend.ImplementClass] = {
    global.compilationUnits
      .filter(_.pkgName == impl.path.pkgName)
      .view
      .flatMap(_.topDefs)
      .collect { case impl: frontend.ImplementClass => impl }
      .find(_.symbol == impl)
  }

  def findImplClassTree(term: Symbol.TermSymbol, global: GlobalData): Option[frontend.ImplementClass] = {
    global.compilationUnits
      .filter(_.pkgName == term.path.pkgName)
      .view
      .flatMap(_.topDefs)
      .collect { case impl: frontend.ImplementClass => impl }
      .find(_.components.exists(_.symbol == term))
  }

  def findImplInterfaceTree(term: Symbol.TermSymbol, global: GlobalData): Option[frontend.ImplementInterface] = {
    global.compilationUnits
      .filter(_.pkgName == term.path.pkgName)
      .view
      .flatMap(_.topDefs)
      .collect { case impl: frontend.ImplementInterface => impl }
      .find(_.methods.exists(_.symbol == term))
  }

  def findImplClassTreeFromState(state: Symbol.StateSymbol, global: GlobalData): Option[frontend.ImplementClass] = {
    def hasState(impl: frontend.ImplementClass): Boolean =
      impl.components.view
        .collect { case stage: frontend.StageDef => stage }
        .flatMap(_.states)
        .exists(_.symbol == state)

    global.compilationUnits
      .filter(_.pkgName == state.path.pkgName)
      .view
      .flatMap(_.topDefs)
      .collect { case impl: frontend.ImplementClass => impl }
      .find(hasState)
  }

  def findMethodTree(method: Symbol.MethodSymbol, global: GlobalData): Option[frontend.MethodDef] = {
    global.compilationUnits
      .filter(_.pkgName == method.path.pkgName)
      .view
      .flatMap(_.topDefs)
      .collect {
        case impl: frontend.ImplementClass => impl.components
        case impl: frontend.ImplementInterface => impl.methods
        case method: frontend.MethodDef => Vector(method)
      }
      .flatten
      .collect { case m: frontend.MethodDef => m }
      .find(_.symbol == method)
  }

  def findStageTree(stage: Symbol.StageSymbol, global: GlobalData): Option[frontend.StageDef] = {
    global.compilationUnits
      .filter(_.pkgName == stage.path.pkgName)
      .view
      .flatMap(_.topDefs)
      .collect {
        case impl: frontend.ImplementClass => impl.components
        case impl: frontend.ImplementInterface => impl.methods
      }
      .flatten
      .collect { case s: frontend.StageDef => s }
      .find(_.symbol == stage)
  }

  def findProcTree(proc: Symbol.ProcSymbol, global: GlobalData): Option[frontend.ProcDef] = {
    global.compilationUnits
      .filter(_.pkgName == proc.path.pkgName)
      .view
      .flatMap(_.topDefs)
      .collect { case impl: frontend.ImplementClass => impl.components }
      .flatten
      .collect { case p: frontend.ProcDef => p }
      .find(_.symbol == proc)
  }

  def buildHPTable(
    hps: Vector[Symbol.HardwareParamSymbol],
    callers: Vector[BackendType],
    targets: Vector[Type.RefType]
  ): ListMap[Symbol.HardwareParamSymbol, HPElem] = {
    val initTable = ListMap.from(hps.map(_ -> Option.empty[HPElem]))

    val assigned = (callers zip targets).foldLeft(initTable) {
      case (table, (caller, target)) => (caller.hargs zip target.hardwareParam).foldLeft(table) {
        case (tab, (callerHArg, ident: frontend.Ident)) =>
          val hp = ident.symbol.asHardwareParamSymbol

          if(tab.contains(hp)) tab.updated(hp, Some(callerHArg))
          else tab
        case (tab, _) => tab
      }
    }

    assigned.map {
      case (key, Some(value)) => key -> value
      case (_, None) => throw new ImplementationErrorException("this table should be all assigned")
    }
  }

  def buildHPTable(
    hps: Vector[Symbol.HardwareParamSymbol],
    caller: BackendType,
    target: Type.RefType
  ): ListMap[Symbol.HardwareParamSymbol, HPElem] = buildHPTable(hps, Vector(caller), Vector(target))

  def buildTPTable(
    tps: Vector[Symbol.TypeParamSymbol],
    caller: BackendType,
    target: Type.RefType
  ): ListMap[Symbol.TypeParamSymbol, BackendType] = buildTPTable(tps, Vector(caller), Vector(target))

  def buildTPTable(
    tps: Vector[Symbol.TypeParamSymbol],
    callers: Vector[BackendType],
    targets: Vector[Type.RefType]
  ): ListMap[Symbol.TypeParamSymbol, BackendType] = {
    def loop(
      table: ListMap[Symbol.TypeParamSymbol, Option[BackendType]],
      callerSide: BackendType,
      targetSide: Type.RefType
    ): ListMap[Symbol.TypeParamSymbol, Option[BackendType]] = {
      val tableList = table.keys.toVector

      targetSide.origin match {
        case tp: Symbol.TypeParamSymbol if tableList.contains(tp) => table.updated(tp, Some(callerSide))
        case _: Symbol.TypeParamSymbol => table
        case _: Symbol.EntityTypeSymbol => (callerSide.targs zip targetSide.typeParam).foldLeft(table) {
          case (t, (caller, target)) => loop(t, caller, target)
        }
      }
    }

    val initTable = ListMap.from(tps.map(_ -> Option.empty[BackendType]))
    val assigned = (callers zip targets).foldLeft(initTable) {
      case (table, (caller, target)) => loop(table, caller, target)
    }
    assigned.map {
      case (key, Some(value)) => key -> value
      case (_, None) => throw new ImplementationErrorException("this table should be all assigned")
    }
  }
}