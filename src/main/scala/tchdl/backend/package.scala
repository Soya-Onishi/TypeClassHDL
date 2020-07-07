package tchdl

import tchdl.{ast => frontend}
import tchdl.util._
import tchdl.util.TchdlException.ImplementationErrorException

import scala.collection.immutable.ListMap

package object backend {
  case class BuiltModule(module: BackendType, impl: Option[ImplementClassContainer], children: Vector[BackendType]) {
    override def hashCode(): Int = module.hashCode() + impl.hashCode + children.hashCode
  }

  trait ToFirrtlString {
    def toFirrtlString: String
  }

  trait HPElem extends ToFirrtlString

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

  case class BackendType(symbol: Symbol.TypeSymbol, hargs: Vector[HPElem], targs: Vector[BackendType]) extends ToFirrtlString {
    override def hashCode(): Int = symbol.hashCode + hargs.hashCode + targs.hashCode
    override def equals(obj: Any): Boolean = obj match {
      case that: BackendType =>
        this.symbol == that.symbol &&
        this.hargs == that.hargs &&
        this.targs == that.targs
      case _ => false
    }

    override def toString: String = {
      val head = symbol.name
      val args = hargs.map(_.toString) ++ targs.map(_.toString)

      args match {
        case Vector() => head
        case args => s"$head[${args.mkString(",")}]"
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
      def loop(verified: BackendType, types: Set[BackendType]): Boolean = {
        verified.symbol match {
          case bit if bit == global.builtin.types.lookup("Bit") => true
          case symbol if global.builtin.types.symbols.contains(symbol) => false
          case symbol: Symbol.EnumSymbol =>
            val memberFieldTypes = symbol.tpe.declares.toMap
              .values.toVector
              .map(_.tpe.asEnumMemberType)
              .flatMap(_.fieldTypes)
            val hpTable = (symbol.hps zip verified.hargs).toMap
            val tpTable = (symbol.tps zip verified.targs).toMap

            memberFieldTypes
              .map(toBackendType(_, hpTable, tpTable))
              .forall(loop(_, types + verified))
          case _ if global.lookupFields(verified).isEmpty => false
          case _ if types(verified) => false
          case _ => global.lookupFields(verified).values.forall(loop(_, types + verified))
        }
      }

      loop(this, Set.empty)
    }
  }

  def toBackendType(tpe: Type.RefType)(implicit global: GlobalData): BackendType = toBackendType(tpe, Map.empty, Map.empty)
  def toBackendType(
    tpe: Type.RefType,
    hpTable: Map[Symbol.HardwareParamSymbol, HPElem],
    tpTable: Map[Symbol.TypeParamSymbol, BackendType]
  )(implicit global: GlobalData): BackendType = {
    def buildFieldTypes(
      signature: BackendType,
      hpTable: Map[Symbol.HardwareParamSymbol, HPElem],
      tpTable: Map[Symbol.TypeParamSymbol, BackendType]
    ): Map[String, BackendType] = {
      signature.symbol.tpe.declares.toMap.collect {
        case (fieldName, field) if field.hasFlag(Modifier.Field) =>
          val tpe = field.tpe.asRefType
          val fieldHArgs = tpe.hardwareParam.map(evalHPExpr(_, hpTable))
          val fieldTArgs = tpe.typeParam.map(toBackendType(_, hpTable, tpTable))
          val signature = BackendType(tpe.origin, fieldHArgs, fieldTArgs)

          fieldName -> signature
      }
    }

    def replace(tpe: Type.RefType): BackendType = tpe.origin match {
      case _: Symbol.EntityTypeSymbol =>
        val hargs = tpe.hardwareParam.map(evalHPExpr(_, hpTable))
        val targs = tpe.typeParam.map(replace)

        val fieldHPTable = (tpe.origin.hps zip hargs).toMap
        val fieldTPTable = (tpe.origin.tps zip targs).toMap

        val backendType = BackendType(tpe.origin, hargs, targs)

        backendType
      case tp: Symbol.TypeParamSymbol =>
        tpTable.getOrElse(tp, throw new ImplementationErrorException(s"$tp should be found in tpTable"))
    }

    replace(tpe)
  }

  def toRefType(sig: BackendType): Type.RefType = {
    def intoLiteral(elem: HPElem): frontend.HPExpr = elem match {
      case HPElem.Num(value) => frontend.IntLiteral(value)
      case HPElem.Str(value) => frontend.StringLiteral(value)
    }

    val hargs = sig.hargs.map(intoLiteral)
    val targs = sig.targs.map(toRefType)

    Type.RefType(sig.symbol, hargs, targs)
  }

  def evalHPExpr(hpExpr: frontend.HPExpr, hpTable: Map[Symbol.HardwareParamSymbol, HPElem]): HPElem =
    hpExpr match {
      case ident: frontend.Ident => hpTable.getOrElse(ident.symbol.asHardwareParamSymbol, throw new ImplementationErrorException("hardware parameter must be found"))
      case frontend.IntLiteral(value) => HPElem.Num(value)
      case frontend.StringLiteral(value) => HPElem.Str(value)
      case frontend.HPBinOp(op, left, right) =>
        val HPElem.Num(leftValue) = evalHPExpr(left, hpTable)
        val HPElem.Num(rightValue) = evalHPExpr(right, hpTable)

        op match {
          case frontend.Operation.Add => HPElem.Num(leftValue + rightValue)
          case frontend.Operation.Sub => HPElem.Num(leftValue - rightValue)
          case frontend.Operation.Mul => HPElem.Num(leftValue * rightValue)
          case frontend.Operation.Div => HPElem.Num(leftValue / rightValue)
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
    ): ListMap[Symbol.TypeParamSymbol, Option[BackendType]] =
      (callerSide.targs zip targetSide.typeParam).foldLeft(table) {
        case (tab, (callerTArg, tpe)) => tpe.origin match {
          case tp: Symbol.TypeParamSymbol if tab.contains(tp) => tab.updated(tp, Some(callerTArg))
          case _: Symbol.TypeParamSymbol => tab
          case _: Symbol.EntityTypeSymbol => (callerTArg.targs zip tpe.typeParam).foldLeft(tab) {
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

  class TempCounter {
    var count = 0

    def get(): Int = {
      val next = count + 1
      count = next

      next
    }
  }
}