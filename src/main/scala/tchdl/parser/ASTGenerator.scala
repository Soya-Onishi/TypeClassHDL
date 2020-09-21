package tchdl.parser

import org.antlr.v4.runtime.tree.TerminalNode
import tchdl.ast._
import tchdl.util._
import tchdl.antlr.{TchdlParser => TP}
import tchdl.util.TchdlException.ImplementationErrorException

import scala.collection.JavaConverters._

case class Filename(name: String)

class ASTGenerator {
  def apply(ctx: TP.Compilation_unitContext, filename: String): CompilationUnit = {
    val pkgName = ctx.pkg_name.EXPR_ID.asScala.map(_.getText).toVector
    val file = Filename(filename)

    val imports = ctx.import_clause
      .asScala
      .map(ctx => packageSelect(ctx.pkg_select)(file) :+ ctx.TYPE_ID.getText)
      .toVector

    val defs = ctx.top_definition.asScala.map(topDefinition(_)(file)).toVector

    CompilationUnit(filename, pkgName, imports, defs, Position(ctx)(file))
  }

  def packageSelect(ctx: TP.Pkg_selectContext)(implicit file: Filename): Vector[String] = ctx match {
    case ctx: TP.PackageIDContext => Vector(ctx.EXPR_ID.getText)
    case ctx: TP.PackageSelectContext => packageSelect(ctx.pkg_select) :+ ctx.EXPR_ID.getText
  }

  def topDefinition(ctx: TP.Top_definitionContext)(implicit file: Filename): Definition = {
    ctx.getChild(0) match {
      case ctx: TP.Module_defContext => moduleDef(ctx)
      case ctx: TP.Method_defContext => methodDef(ctx)
      case ctx: TP.Struct_defContext => structDef(ctx)
      case ctx: TP.Trait_defContext => traitDef(ctx)
      case ctx: TP.Enum_defContext => enumDef(ctx)
      case ctx: TP.Interface_defContext => interfaceDef(ctx)
      case ctx: TP.Implement_classContext => implementClass(ctx)
      case ctx: TP.Implement_interfaceContext => implementInterface(ctx)
    }
  }

  def moduleDef(ctx: TP.Module_defContext)(implicit file: Filename): ModuleDef = {
    val name = ctx.TYPE_ID.getText
    val (hp, tp, bound) = definitionHeader(ctx.type_param(), ctx.bounds())

    def fields[T](ctx: T, flag: Modifier)(ids: T => java.util.List[TerminalNode])(tpes: T => java.util.List[TP.TypeContext]): Vector[ValDef] = {
      val ctxOpt = Option(ctx)
      val nodeNames = ctxOpt.map(ctx => ids(ctx)).map(_.asScala.toVector).getOrElse(Vector.empty)
      val nodeTpes = ctxOpt.map(ctx => tpes(ctx)).map(_.asScala.map(typeTree).toVector).getOrElse(Vector.empty)

      (nodeNames zip nodeTpes).map{
        case (name, tpe) =>
          val start = Point(name.getSymbol.getLine, name.getSymbol.getCharPositionInLine)
          val end = tpe.position.end
          val pos = Position(file.name, start, end)

          ValDef(flag | Modifier.Field, name.getText, Some(tpe), None, pos)
      }
    }

    val parents = fields(ctx.parents, Modifier.Parent)(_.EXPR_ID)(_.`type`)
    val siblings = fields(ctx.siblings, Modifier.Sibling)(_.EXPR_ID)(_.`type`)

    ModuleDef(name, hp, tp, bound, parents, siblings, Position(ctx))
  }

  def structDef(ctx: TP.Struct_defContext)(implicit file: Filename): StructDef = {
    val name = ctx.TYPE_ID.getText
    val (hp, tp, bound) = definitionHeader(ctx.type_param(), ctx.bounds())
    val fields = Option(ctx.field_defs).map(fieldDefs).getOrElse(Vector.empty)

    StructDef(name, hp, tp, bound, fields, Position(ctx))
  }

  def implementClass(ctx: TP.Implement_classContext)(implicit file: Filename): ImplementClass = {
    val target = typeTree(ctx.`type`())
    val (hps, tps) = Option(ctx.type_param).map(polyParam).getOrElse((Vector.empty, Vector.empty))
    val bounds = Option(ctx.bounds).map(_.bound.asScala.map(bound).toVector).getOrElse(Vector.empty)
    val components = ctx.component.asScala.map(component).toVector

    ImplementClass(target, hps, tps, bounds, components, Position(ctx))
  }

  def traitDef(ctx: TP.Trait_defContext)(implicit file: Filename): InterfaceDef = {
    val name = ctx.TYPE_ID.getText
    val (hp, tp, bound) = definitionHeader(ctx.type_param, ctx.bounds)
    val methods = ctx.signature_def
      .asScala
      .map(signatureDef)
      .toVector

    val types = ctx.type_dec.asScala
      .map(ctx => TypeDef(Modifier.Field, ctx.TYPE_ID.getText, None, Position(ctx)))
      .toVector

    InterfaceDef(Modifier.Trait, name, hp, tp, bound, methods, types, Position(ctx))
  }

  def interfaceDef(ctx: TP.Interface_defContext)(implicit file: Filename): InterfaceDef = {
    val name = ctx.TYPE_ID.getText
    val (hp, tp, bound) = definitionHeader(ctx.type_param, ctx.bounds)
    val methods = ctx.signature_def
      .asScala
      .map(signatureDef)
      .toVector

    val types = ctx.type_dec.asScala
      .map(ctx => TypeDef(Modifier.Field, ctx.TYPE_ID.getText, None, Position(ctx)))
      .toVector

    InterfaceDef(Modifier.Interface, name, hp, tp, bound, methods, types, Position(ctx))
  }

  def enumDef(ctx: TP.Enum_defContext)(implicit file: Filename): EnumDef = {
    def enumFieldDef(ctx: TP.Enum_field_defContext): EnumMemberDef = {
      val fieldName = ctx.TYPE_ID.getText
      val fields = ctx.`type`.asScala.map(typeTree).toVector

      EnumMemberDef(fieldName, fields, Position(ctx))
    }

    val enumName = ctx.TYPE_ID.getText
    val (hps, tps, bounds) = definitionHeader(ctx.type_param, ctx.bounds)
    val fields = ctx.enum_field_def.asScala.map(enumFieldDef).toVector

    EnumDef(enumName, hps, tps, bounds, fields, Position(ctx))
  }

  def implementInterface(ctx: TP.Implement_interfaceContext)(implicit file: Filename): ImplementInterface = {
    val (hp, tp, bound) = definitionHeader(ctx.type_param(), ctx.bounds())
    val Seq(targetTrait, tpe) = ctx.`type`().asScala.map(typeTree)
    val methods = ctx.method_def.asScala.map(methodDef).toVector
    val tpes = ctx.type_def.asScala.map(typeDef).toVector

    ImplementInterface(targetTrait, tpe, hp, tp, bound, methods, tpes, Position(ctx))
  }

  def typeDef(ctx: TP.Type_defContext)(implicit file: Filename): TypeDef = {
    val name = ctx.TYPE_ID.getText
    val tpe = Option(ctx.`type`).map(typeTree)

    TypeDef(Modifier.Field, name, tpe, Position(ctx))
  }

  def methodDef(ctx: TP.Method_defContext)(implicit file: Filename): MethodDef = {
    def builtin(ctx: TP.Builtin_specifierContext): Annotation = {
      val name = ctx.EXPR_ID.getText
      val tpes = ctx.builtin_type.asScala.toVector.map {
        case ctx: TP.UseIDPatternContext => ctx.TYPE_ID.getText
        case _: TP.AnyPatternContext => "*"
      }

      Annotation.BuiltIn(name, tpes.init, tpes.last)
    }

    val builtins = ctx.builtin_specifier.asScala.map(builtin).toVector
    val modifier = ctx.method_accessor.asScala
      .map(_.getText)
      .map(Modifier.apply)
      .foldLeft[Modifier](Modifier.NoModifier){ case (acc, modifier) => acc | modifier }

    val name = ctx.EXPR_ID.getText
    val (hps, tps, bounds) = definitionHeader(ctx.type_param(), ctx.bounds())
    val params = Option(ctx.param_defs())
      .map(paramDefs)
      .getOrElse(Vector.empty)
    val tpe = typeTree(ctx.`type`)
    val blk = block(ctx.block)

    MethodDef(builtins, modifier, name, hps, tps, bounds, params, tpe, Some(blk), Position(ctx))
  }

  def signatureDef(ctx: TP.Signature_defContext)(implicit file: Filename): MethodDef = {
    val modifier = ctx.signature_accessor.asScala
      .map(_.getText)
      .map(Modifier.apply)
      .foldLeft[Modifier](Modifier.NoModifier) {
        case (acc, modifier) => acc | modifier
      }

    val name = ctx.EXPR_ID.getText
    val (hps, tps, bounds) = definitionHeader(ctx.type_param(), ctx.bounds())
    val params = Option(ctx.param_defs())
      .map(paramDefs)
      .getOrElse(Vector.empty)
    val tpe = typeTree(ctx.`type`)

    MethodDef(Vector.empty, modifier, name, hps, tps, bounds, params, tpe, None, Position(ctx))
  }

  def definitionHeader(tpCtx: TP.Type_paramContext, boundsCtx: TP.BoundsContext)(implicit file: Filename): (Vector[ValDef], Vector[TypeDef], Vector[BoundTree]) = {
    val (hps, tps) = Option(tpCtx)
      .map(polyParam)
      .getOrElse(Vector.empty, Vector.empty)

    val bounds = Option(boundsCtx)
      .map(_.bound.asScala.map(bound).toVector)
      .getOrElse(Vector.empty)

    (hps, tps, bounds)
  }

  def fieldDefs(ctx: TP.Field_defsContext)(implicit file: Filename): Vector[ValDef] =
    ctx.field_def.asScala.map(fieldDef).toVector

  def fieldDef(ctx: TP.Field_defContext)(implicit file: Filename): ValDef = {
    val name = ctx.EXPR_ID.getText
    val tpe = typeTree(ctx.`type`())

    ValDef(Modifier.Field, name, Some(tpe), None, Position(ctx))
  }

  def paramDefs(ctx: TP.Param_defsContext)(implicit file: Filename): Vector[ValDef] = {
    Option(ctx.param_def)
      .map(_.asScala.map(paramDef).toVector)
      .getOrElse(Vector.empty)
  }

  def paramDef(ctx: TP.Param_defContext)(implicit file: Filename): ValDef = {
    val name = ctx.EXPR_ID.getText
    val tpe = typeTree(ctx.`type`())

    ValDef(Modifier.Local, name, Some(tpe), None, Position(ctx))
  }

  def alwaysDef(ctx: TP.Always_defContext)(implicit file: Filename): AlwaysDef = {
    val name = ctx.EXPR_ID.getText
    val blk = block(ctx.block)

    AlwaysDef(name, blk, Position(ctx))
  }

  def valDef(ctx: TP.Val_defContext)(implicit file: Filename): ValDef = {
    val name = ctx.EXPR_ID.getText
    val tpe = Option(ctx.`type`).map(typeTree)
    val initExpr = expr(ctx.expr)

    ValDef(Modifier.Local, name, tpe, Some(initExpr), Position(ctx))
  }

  def stageDef(ctx: TP.Stage_defContext)(implicit file: Filename): StageDef = {
    def stageBody(ctx: TP.Stage_bodyContext): (Vector[StateDef], Vector[BlockElem]) = {
      val statedefs = ctx.state_def
        .asScala
        .map(stateDef)
        .toVector

      val blockElems = ctx.block_elem
        .asScala
        .map(blockElem)
        .toVector

      (statedefs, blockElems)
    }

    val name = ctx.EXPR_ID.getText
    val params = Option(ctx.param_defs)
      .map(paramDefs)
      .getOrElse(Vector.empty)
    val tpe = typeTree(ctx.`type`)
    val (states, blks) =
      Option(ctx.stage_body)
        .map(stageBody)
        .getOrElse((Vector.empty, Vector.empty))

    StageDef(name, params, tpe, states, blks, Position(ctx))
  }

  def stateDef(ctx: TP.State_defContext)(implicit file: Filename): StateDef = {
    val name = ctx.EXPR_ID.getText
    val blk = block(ctx.block)
    val params = Option(ctx.param_defs).map(paramDefs).getOrElse(Vector.empty)

    StateDef(name, params, blk, Position(ctx))
  }

  def portDef(ctx: TP.Port_defContext)(implicit file: Filename): ValDef = {
    val modifier = Modifier(ctx.modifier.getText) | Modifier.Field
    val name = ctx.EXPR_ID.getText
    val tpe = typeTree(ctx.`type`)

    ValDef(modifier, name, Some(tpe), None, Position(ctx))
  }

  def submoduleDef(ctx: TP.Submodule_defContext)(implicit file: Filename): ValDef = {
    val name = ctx.EXPR_ID.getText
    val tpe = typeTree(ctx.`type`)
    val construct = constructModule(ctx.construct_module)

    ValDef(Modifier.Child | Modifier.Field, name, Some(tpe), Some(construct), Position(ctx))
  }

  def regDef(ctx: TP.Reg_defContext)(implicit file: Filename): ValDef = {
    val name = ctx.EXPR_ID.getText
    val tpe = typeTree(ctx.`type`)
    val initExpr = Option(ctx.expr).map(expr)

    ValDef(Modifier.Register | Modifier.Field, name, Some(tpe), initExpr, Position(ctx))
  }

  def expr(ctx: TP.ExprContext)(implicit file: Filename): Expression = ctx match {
    case ctx: TP.SelectExprContext => selectExpr(ctx)
    case ctx: TP.CastExprContext => CastExpr(expr(ctx.expr), typeTree(ctx.`type`), Position(ctx))
    case ctx: TP.UnaryExprContext => stdUnaryOp(ctx.op.getText, ctx.expr, Position(ctx))
    case ctx: TP.MulDivExprContext => stdBinOp(ctx.expr(0), ctx.expr(1), ctx.op.getText, Position(ctx))
    case ctx: TP.AddSubExprContext => stdBinOp(ctx.expr(0), ctx.expr(1), ctx.op.getText, Position(ctx))
    case ctx: TP.ShiftExprContext => stdBinOp(ctx.expr(0), ctx.expr(1), ctx.op.getText, Position(ctx))
    case ctx: TP.CmpExprContext => stdBinOp(ctx.expr(0), ctx.expr(1), ctx.op.getText, Position(ctx))
    case ctx: TP.EqExprContext => stdBinOp(ctx.expr(0), ctx.expr(1), ctx.op.getText, Position(ctx))
    case ctx: TP.AndExprContext => stdBinOp(ctx.expr(0), ctx.expr(1), "&", Position(ctx))
    case ctx: TP.XorExprContext => stdBinOp(ctx.expr(0), ctx.expr(1), "^", Position(ctx))
    case ctx: TP.OrExprContext => stdBinOp(ctx.expr(0), ctx.expr(1), "|", Position(ctx))
    case ctx: TP.ApplyExprContext => applyCall(ctx.apply)
    case ctx: TP.BlockExprContext => block(ctx.block)
    case ctx: TP.ConstructStructExprContext => constructStruct(ctx.construct_struct)
    case ctx: TP.ConstructModuleExprContext => constructModule(ctx.construct_module)
    case ctx: TP.ConstructEnumExprContext => constructEnum(ctx.construct_enum)
    case ctx: TP.IfExprContext =>
      val cond = expr(ctx.expr(0))
      val conseq = expr(ctx.expr(1))
      val alt = Option(ctx.expr(2)).map(expr)

      IfExpr(cond, conseq, alt, Position(ctx))
    case ctx: TP.MatchExprContext => matchExpr(ctx)
    case ctx: TP.FinishContext => Finish(Position(ctx))
    case ctx: TP.GotoExprContext => goto(ctx.goto_expr)
    case ctx: TP.RelayExprContext => relay(ctx.relay)
    case ctx: TP.GenerateExprContext => generate(ctx.generate)
    case ctx: TP.ReturnContext => Return(expr(ctx.expr), Position(ctx))
    case ctx: TP.LitExprContext => literal(ctx.literal)
    case ctx: TP.ParenthesesExprContext => expr(ctx.expr)
    case ctx: TP.SelfExprContext => This(Position(ctx))
    case ctx: TP.ExprIDContext => Ident(ctx.EXPR_ID.getText, Position(ctx))
  }

  def hpExpr(ctx: TP.Hp_exprContext)(implicit file: Filename): HPExpr = ctx match {
    case ctx: TP.AddSubHPExprContext => hpBinOp(ctx.hp_expr(0), ctx.hp_expr(1), ctx.op.getText)
    case ctx: TP.StrLitHPExprContext => StringLiteral(ctx.STRING.getText.tail.init, Position(ctx))
    case ctx: TP.IntLitHPExprContext => IntLiteral(ctx.INT.getText.toInt, Position(ctx))
    case ctx: TP.HPExprIDContext => Ident(ctx.getText, Position(ctx))
  }

  def selectExpr(ctx: TP.SelectExprContext)(implicit file: Filename): Expression = Option(ctx.apply) match {
    case Some(applyCtx) =>
      val prefix = expr(ctx.expr)

      applyCall(applyCtx) match {
        case apply @ Apply(Ident(name), hps, tps, args) =>
          val selectPos = Position(prefix, apply.prefix)
          val select = Select(prefix, name, selectPos)

          Apply(select, hps, tps, args, apply.position)
        case Apply(expr, _, _, _) =>
          val msg = s"${expr.getClass} must not appear here"
          throw new ImplementationErrorException(msg)
      }
    case None =>
      val prefix = expr(ctx.expr)
      val name = ctx.EXPR_ID.getText

      val startPos = prefix.position.start
      val endPos = Point(ctx.EXPR_ID.getSymbol.getLine, ctx.EXPR_ID.getSymbol.getCharPositionInLine)
      val pos = Position(file.name, startPos, endPos)

      Select(prefix, name, pos)
  }

  def matchExpr(ctx: TP.MatchExprContext)(implicit file: Filename): Match = {
    def pattern(ctx: TP.PatternContext): MatchPattern = ctx match {
      case ctx: TP.IdentPatternContext =>
        val symbol = ctx.EXPR_ID.getSymbol
        val line = symbol.getLine
        val startColumn = symbol.getCharPositionInLine
        val endColumn = startColumn + ctx.EXPR_ID.getText.length
        val identPos = Position(file.name, Point(line, startColumn), Point(line, endColumn))

        IdentPattern(Ident(ctx.EXPR_ID.getText, identPos), Position(ctx))
      case ctx: TP.LiteralPatternContext => LiteralPattern(literal(ctx.literal), Position(ctx))
      case ctx: TP.WildcardPatternContext => WildCardPattern(Position(ctx))
      case ctx: TP.EnumPatternContext =>
        val variant = typeTree(ctx.`type`)
        val patterns = ctx.pattern.asScala.map(pattern).toVector

        EnumPattern(variant, patterns, Position(ctx))
    }

    def caseDef(ctx: TP.Case_defContext): Case = {
      val patternExpr = pattern(ctx.pattern)
      val blkElems = ctx.block_elem.asScala.map(blockElem).toVector
      val body = blkElems.lastOption match {
        case None => Vector(UnitLiteral(Position(ctx)))
        case Some(vdef: ValDef) => blkElems.init ++ Vector(vdef, UnitLiteral(vdef.position))
        case Some(expr) => blkElems.init :+ expr
      }

      Case(patternExpr, body, Position(ctx))
    }

    val matched = expr(ctx.expr)
    val cases = ctx.case_def.asScala.map(caseDef).toVector

    Match(matched, cases, Position(ctx))
  }

  def stdUnaryOp(op: String, exp: TP.ExprContext, position: Position)(implicit file: Filename): StdUnaryOp = {
    val operation = op match {
      case "-" => Operation.Neg
      case "!" => Operation.Not
    }

    StdUnaryOp(operation, expr(exp), position)
  }

  def stdBinOp(left: TP.ExprContext, right: TP.ExprContext, op: String, position: Position)(implicit file: Filename): StdBinOp = {
    val operation = op match {
      case "+"  => Operation.Add
      case "-"  => Operation.Sub
      case "*"  => Operation.Mul
      case "/"  => Operation.Div
      case "|"  => Operation.Or
      case "&"  => Operation.And
      case "^"  => Operation.Xor
      case ">>" => Operation.Shr
      case "<<" => Operation.Shl
      case ">>>" => Operation.DynShr
      case "<<<" => Operation.DynShl
      case "==" => Operation.Eq
      case "!=" => Operation.Ne
      case "<"  => Operation.Lt
      case "<=" => Operation.Le
      case ">"  => Operation.Gt
      case ">=" => Operation.Ge
    }

    StdBinOp(operation, expr(left), expr(right), position)
  }

  def hpBinOp(left: TP.Hp_exprContext, right: TP.Hp_exprContext, op: String)(implicit file: Filename): HPBinOp = {
    def neg(expr: HPExpr): HPExpr = expr match {
      case HPUnaryOp(ident) => ident
      case ident: Ident => HPUnaryOp(ident, ident.position)
      case bin @ HPBinOp(left, right) => HPBinOp(neg(left), neg(right), bin.position)
      case lit @ IntLiteral(value) => IntLiteral(-value, lit.position)
      case others => others
    }

    val l = hpExpr(left)
    val r = hpExpr(right)

    val position = Position(file.name, l.position.start, r.position.end)
    op match {
      case "+" => HPBinOp(l, r, position)
      case "-" => HPBinOp(l, neg(r), position)
    }
  }

  def typeTree(ctx: TP.TypeContext)(implicit file: Filename): TypeTree = {
    ctx match {
      case ctx: TP.RawTypeContext => rawTypeTree(ctx.raw_type)
      case ctx: TP.PointerTypeContext =>
        val tree = rawTypeTree(ctx.raw_type)
        tree.copy(isPointer = true)
    }
  }

  def rawTypeTree(ctx: TP.Raw_typeContext)(implicit file: Filename): TypeTree = {
    def typeCast(ctx: TP.TypeCastContext): TypeTree = {
      val from = rawTypeTree(ctx.raw_type(0))
      val to = rawTypeTree(ctx.raw_type(1))
      val cast = CastType(from, to, Position(ctx))

      TypeTree(cast, Vector.empty, Vector.empty, false, Position(ctx))
    }

    def typeHead(ctx: TP.TypeHeadContext): TypeTree = {
      val pkg = Option(ctx.pkg_select).map(packageSelect).getOrElse(Vector.empty)
      val elem = typeElem(ctx.type_elem)

      if(pkg.isEmpty) elem
      else {
        val TypeTree(ident @ Ident(name), hargs, targs, pExpr) = elem
        val start = Position(ctx.pkg_select).start
        val end = ident.position.end
        val pos = Position(file.name, start, end)

        val head = SelectPackage(pkg, name, pos)

        TypeTree(head, hargs, targs, pExpr, Position(ctx))
      }
    }

    def typeSelect(ctx: TP.TypeSelectContext): TypeTree = {
      val head = rawTypeTree(ctx.raw_type)
      val tree @ TypeTree(Ident(name), hargs, targs, defaultExpr) = typeElem(ctx.type_elem)
      val endLine = head.position.end.line
      val endColumn = head.position.end.column + name.length
      val endPos = Point(endLine, endColumn)
      val selectPos = Position(file.name, head.position.start, endPos)
      val select = StaticSelect(head, name, selectPos)

      TypeTree(select, hargs, targs, defaultExpr, tree.position)
    }

    ctx match {
      case ctx: TP.TypeCastContext => typeCast(ctx)
      case ctx: TP.TypeHeadContext => typeHead(ctx)
      case ctx: TP.TypeSelectContext => typeSelect(ctx)
      case ctx: TP.TypeParenthesesContext => rawTypeTree(ctx.raw_type)
    }
  }

  def typeElem(ctx: TP.Type_elemContext)(implicit file: Filename): TypeTree = {
    ctx match {
      case ctx: TP.NormalTypeContext =>
        val idLine = ctx.TYPE_ID.getSymbol.getLine
        val idStartColumn = ctx.TYPE_ID.getSymbol.getCharPositionInLine
        val idEndColumn = ctx.TYPE_ID.getText.length + idStartColumn
        val idPos = Position(file.name, Point(idLine, idStartColumn), Point(idLine, idEndColumn))
        val id = Ident(ctx.TYPE_ID.getText, idPos)

        Option(ctx.apply_typeparam).map(applyTypeParam) match {
          case Some((hps, tps)) => TypeTree(id, hps, tps, isPointer = false, Position(ctx))
          case None => TypeTree(id, Vector.empty, Vector.empty, isPointer = false, Position(ctx))
        }
      case ctx: TP.ThisTypeContext =>
        TypeTree(ThisType(Position(ctx)), Vector.empty, Vector.empty, isPointer = false, Position(ctx))
    }
  }

  def applyCall(ctx: TP.ApplyContext)(implicit file: Filename): Apply = {
    val head = Option(ctx.`type`).map(typeTree)

    val name = ctx.EXPR_ID.getText
    val (hargs, targs) = Option(ctx.apply_typeparam).map(applyTypeParam).getOrElse(Vector.empty, Vector.empty)
    val args = ctx.args.expr.asScala.map(expr).toVector

    val prefix = head match {
      case Some(tree) =>
        val endLine = tree.position.end.line
        val endColumn = tree.position.end.column + name.length
        val pos = Position(tree.position.filename, tree.position.start, Point(endLine, endColumn))

        StaticSelect(tree, name, pos)
      case None =>
        val line = ctx.EXPR_ID.getSymbol.getLine
        val startColumn = ctx.EXPR_ID.getSymbol.getCharPositionInLine
        val endColumn = startColumn + name.length
        val pos = Position(file.name, Point(line, startColumn), Point(line, endColumn))

        Ident(name, pos)
    }

    Apply(prefix, hargs, targs, args, Position(ctx))
  }

  def polyParam(ctx: TP.Type_paramContext)(implicit file: Filename): (Vector[ValDef], Vector[TypeDef]) = {
    def tparam(id: TerminalNode): TypeDef = {
      val line = id.getSymbol.getLine
      val startColumn = id.getSymbol.getCharPositionInLine
      val endColumn = startColumn + id.getText.length
      val start = Point(line, startColumn)
      val end = Point(line, endColumn)

      TypeDef(Modifier.Param, id.getText, None, Position(file.name, start, end))
    }

    ctx match {
      case ctx: TP.WithDependencyContext =>
        val hps = paramDefs(ctx.param_defs)
        val tps = ctx.TYPE_ID().asScala.map(tparam).toVector

        (hps, tps)
      case ctx: TP.WithoutDependencyContext =>
        val tps = ctx.TYPE_ID().asScala.map(tparam).toVector

        (Vector.empty, tps)
    }
  }

  def applyTypeParam(ctx: TP.Apply_typeparamContext)(implicit file: Filename): (Vector[HPExpr], Vector[TypeTree]) = ctx match {
    case ctx: TP.WithHardwareParamsContext =>
      val exprs = hardwareParams(ctx.hardware_params)
      val tpes = Option(ctx.type_params).map(typeParams).getOrElse(Vector.empty)

      (exprs, tpes)
    case ctx: TP.WithoutHardwareParamsContext =>
      val tpes = typeParams(ctx.type_params)

      (Vector.empty, tpes)
  }

  def hardwareParams(ctx: TP.Hardware_paramsContext)(implicit file: Filename): Vector[HPExpr] =
    ctx.hp_expr.asScala.map(hpExpr).toVector

  def typeParams(ctx: TP.Type_paramsContext)(implicit file: Filename): Vector[TypeTree] =
    ctx.`type`.asScala.map(typeTree).toVector


  def block(ctx: TP.BlockContext)(implicit file: Filename): Block = {
    val elems = ctx.block_elem
      .asScala
      .map(blockElem)
      .toVector

    elems match {
      case Vector() => Block(Vector.empty, UnitLiteral(Position(ctx)), Position(ctx))
      case elems => elems.last match {
        case e: Expression => Block(elems.dropRight(1), e, Position(ctx))
        case _: ValDef     => Block(elems, UnitLiteral(Position(ctx)), Position(ctx))
        case _: Assign     => Block(elems, UnitLiteral(Position(ctx)), Position(ctx))
      }
    }
  }

  def blockElem(ctx: TP.Block_elemContext)(implicit file: Filename): BlockElem = ctx match {
    case ctx: TP.ValDefPatternContext => valDef(ctx.val_def)
    case ctx: TP.ExprPatternContext => expr(ctx.expr)
    case ctx: TP.AssignPatternContext =>
      val loc = expr(ctx.expr(0))
      val rhs = expr(ctx.expr(1))

      Assign(loc, rhs, Position(ctx))
  }

  def constructStruct(ctx: TP.Construct_structContext)(implicit file: Filename): ConstructClass = {
    val tpe = typeTree(ctx.`type`)
    val pairs = Option(ctx.construct_pair)
      .map(_.asScala.map(ctx => ConstructPair(ctx.EXPR_ID.getText, expr(ctx.expr), Position(ctx))).toVector)
      .getOrElse(Vector.empty)

    ConstructClass(tpe, pairs, Position(ctx))
  }

  def constructModule(ctx: TP.Construct_moduleContext)(implicit file: Filename): ConstructModule = {
    val tpe = typeTree(ctx.`type`)

    val parents = Option(ctx.parent_pair)
      .map(_.asScala.map(ctx => ConstructPair(ctx.EXPR_ID.getText, expr(ctx.expr), Position(ctx))))
      .getOrElse(Seq.empty)
      .toVector

    val siblings = Option(ctx.sibling_pair)
      .map(_.asScala.map(ctx => ConstructPair(ctx.EXPR_ID.getText, expr(ctx.expr), Position(ctx))))
      .getOrElse(Seq.empty)
      .toVector

    ConstructModule(tpe, parents, siblings, Position(ctx))
  }

  def constructEnum(ctx: TP.Construct_enumContext)(implicit file: Filename): ConstructEnum = {
    val target = typeTree(ctx.`type`)
    val fields = ctx.expr.asScala.map(expr).toVector

    ConstructEnum(target, fields, Position(ctx))
  }

  def bound(ctx: TP.BoundContext)(implicit file: Filename): BoundTree = {
    def hpBoundExpr(ctx: TP.Hp_bound_exprContext): RangeExpr = ctx match {
      case ctx: TP.MaxBoundContext => RangeExpr.Max(hpExpr(ctx.hp_expr))
      case ctx: TP.MinBoundContext => RangeExpr.Min(hpExpr(ctx.hp_expr))
      case ctx: TP.EqBoundContext => RangeExpr.EQ(hpExpr(ctx.hp_expr))
    }

    ctx match {
      case ctx: TP.TPBoundContext =>
        val identSymbol = ctx.TYPE_ID.getSymbol
        val identLine = identSymbol.getLine
        val identStart = identSymbol.getCharPositionInLine
        val identEnd = identStart + ctx.TYPE_ID.getText.length
        val identPos = Position(file.name, Point(identLine, identStart), Point(identLine, identEnd))

        val target = TypeTree(Ident(ctx.TYPE_ID.getText, identPos), Vector.empty, Vector.empty, false, identPos)
        val bounds = ctx.`type`.asScala.map(typeTree)

        TPBoundTree(target, bounds.toVector, Position(ctx))
      case ctx: TP.HPBoundContext =>
        val target = hpExpr(ctx.hp_expr)
        val bounds = ctx.hp_bound_expr.asScala.map(hpBoundExpr).toVector

        HPBoundTree(target, bounds, Position(ctx))
    }
  }

  def generate(ctx: TP.GenerateContext)(implicit file: Filename): Generate = {
    val stageArgs = ctx.args(0).expr.asScala.map(expr).toVector
    val stateArgs = Option(ctx.args(1))
      .map(_.expr.asScala.toVector)
      .getOrElse(Vector.empty)
      .map(expr)

    val stageName = ctx.EXPR_ID(0).getText
    val stateName = Option(ctx.EXPR_ID(1)).map(_.getText)

    val stateNameLine = Option(ctx.EXPR_ID(1)).map(_.getSymbol.getLine)
    val stateNameStart = Option(ctx.EXPR_ID(1)).map(_.getSymbol.getCharPositionInLine)
    val stateInfoEnd = Position(ctx).end
    val stateInfoPos = (stateNameLine zip stateNameStart)
      .map{ case (line, start) => Position(file.name, Point(line, start), stateInfoEnd) }
      .headOption

    val state = stateName match {
      case None => None
      case Some(name) => Some(StateInfo(name, stateArgs, stateInfoPos.get))
    }

    Generate(stageName, stageArgs, state, Position(ctx))
  }

  def relay(ctx: TP.RelayContext)(implicit file: Filename): Relay = {
    val stageArgs = ctx.args(0).expr.asScala.map(expr).toVector
    val stateArgs = Option(ctx.args(1))
      .map(_.expr.asScala.toVector)
      .getOrElse(Vector.empty)
      .map(expr)

    val stageName = ctx.EXPR_ID(0).getText
    val stateName = Option(ctx.EXPR_ID(1)).map(_.getText)
    val stateNameLine = Option(ctx.EXPR_ID(1)).map(_.getSymbol.getLine)
    val stateNameStart = Option(ctx.EXPR_ID(1)).map(_.getSymbol.getCharPositionInLine)
    val stateInfoEnd = Position(ctx).end
    val stateInfoPos = (stateNameLine zip stateNameStart)
      .map{ case (line, start) => Position(file.name, Point(line, start), stateInfoEnd) }
      .headOption

    val state = stateName match {
      case None => None
      case Some(name) => Some(StateInfo(name, stateArgs, stateInfoPos.get))
    }

    Relay(stageName, stageArgs, state, Position(ctx))
  }

  def goto(ctx: TP.Goto_exprContext)(implicit file: Filename): Goto = {
    val args = Option(ctx.args)
      .map(_.expr.asScala.map(expr).toVector)
      .getOrElse(Vector.empty)

    Goto(ctx.EXPR_ID.getText, args, Position(ctx))
  }

  def literal(ctx: TP.LiteralContext)(implicit file: Filename): Literal = ctx match {
    case ctx: TP.BitLitContext =>
      val raw = ctx.BIT.getText.substring(2)
      BitLiteral(BigInt(raw, 2), raw.length, Position(ctx))
    case ctx: TP.IntLitContext =>
      ctx.INT.getText.toIntOption match {
        case Some(value) => IntLiteral(value, Position(ctx))
        case None => ???
      }
    case ctx: TP.TrueLitContext => BoolLiteral(value = true, Position(ctx))
    case ctx: TP.FalseLitContext => BoolLiteral(value = false, Position(ctx))
    case ctx: TP.UnitLitContext => UnitLiteral(Position(ctx))
  }

  def component(ctx: TP.ComponentContext)(implicit file: Filename): Component = ctx.getChild(0) match {
    case ctx: TP.Port_defContext   => portDef(ctx)
    case ctx: TP.Submodule_defContext => submoduleDef(ctx)
    case ctx: TP.Reg_defContext    => regDef(ctx)
    case ctx: TP.Method_defContext => methodDef(ctx)
    case ctx: TP.Stage_defContext  => stageDef(ctx)
    case ctx: TP.Always_defContext => alwaysDef(ctx)
  }
}
