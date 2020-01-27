package tchdl.parser

import tchdl.ast._
import tchdl.util.Modifier
import tchdl.antlr.{TchdlParser => TP}
import scala.jdk.CollectionConverters._

class ASTGenerator {
  def apply(ctx: TP.Compilation_unitContext, filename: String): CompilationUnit = {
    val defs = ctx.top_definition.asScala.map(topDefinition).toVector

    CompilationUnit(Some(filename), defs)
  }

  def topDefinition(ctx: TP.Top_definitionContext): Definition = {
    ctx.getChild(0) match {
      case ctx: TP.Module_defContext => moduleDef(ctx)
      case ctx: TP.Method_defContext => methodDef(ctx)
      case ctx: TP.Struct_defContext => structDef(ctx)
    }
  }

  def moduleDef(ctx: TP.Module_defContext): ModuleDef = {
    val (name, hp, tp, bound) = template(ctx.template)
    val otherModules = Option(ctx.field_defs())
      .map(fieldDefs)
      .getOrElse(Vector.empty)

    val components = ctx.component
      .asScala
      .map(component)
      .toVector

    ModuleDef(name, hp, tp, bound, otherModules, components)
  }

  def structDef(ctx: TP.Struct_defContext): StructDef = {
    val (name, hp, tp, bound) = template(ctx.template)
    val fields = fieldDefs(ctx.field_defs)

    StructDef(name, hp, tp, bound, fields)
  }

  def methodDef(ctx: TP.Method_defContext): MethodDef = {
    val (name, hp, tp, bound) = template(ctx.template)
    val params = fieldDefs(ctx.field_defs)
    val tpe = typeTree(ctx.`type`)
    val blk = Option(ctx.block).map(block)

    MethodDef(name, hp, tp, bound, params, tpe, blk)
  }

  def template(ctx: TP.TemplateContext): (String, Vector[FieldDef], Vector[TypeDef], Vector[Bound]) = {
    val name = ctx.ID.getText

    val hp = Option(ctx.hardware_param)
      .map(ctx => fieldDefs(ctx.field_defs))
      .getOrElse(Vector.empty)

    val tp = Option(ctx.type_param)
      .map(_.ID.asScala.map(_.getText).map(TypeDef.apply).toVector)
      .getOrElse(Vector.empty)

    val bounds = Option(ctx.bounds)
      .map(_.bound.asScala.map(bound).toVector)
      .getOrElse(Vector.empty)

    (name, hp, tp, bounds)
  }

  def fieldDefs(ctx: TP.Field_defsContext): Vector[FieldDef] =
    Option(ctx.field_def)
      .map(_.asScala.map(fieldDef).toVector)
      .getOrElse(Vector.empty)

  def fieldDef(ctx: TP.Field_defContext): FieldDef = {
    val modifier = Modifier(ctx.modifier
      .asScala
      .map(_.getChild(0).getText)
      .toVector
    )

    val name = ctx.ID.getText
    val tpe = typeTree(ctx.`type`())

    FieldDef(modifier, name, tpe)
  }

  def alwaysDef(ctx: TP.Always_defContext): AlwaysDef = {
    val name = ctx.ID.getText
    val blk = block(ctx.block)

    AlwaysDef(name, blk)
  }

  def valDef(ctx: TP.Val_defContext): ValDef = {
    val name = ctx.ID.getText
    val tpe = Option(ctx.`type`).map(typeTree)
    val initExpr = expr(ctx.expr)

    ValDef(Modifier.NoModifier, name, tpe, Some(initExpr))
  }

  def stageDef(ctx: TP.Stage_defContext): StageDef = {
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

    val name = ctx.ID.getText
    val params = fieldDefs(ctx.field_defs)
    val tpe = typeTree(ctx.`type`)
    val (states, blks) = Option(ctx.stage_body).map(stageBody) match {
      case Some((states, blks)) => (Some(states), Some(blks))
      case None => (None, None)
    }

    StageDef(name, params, tpe, states, blks)
  }

  def stateDef(ctx: TP.State_defContext): StateDef = {
    val name = ctx.ID.getText
    val blk = block(ctx.block)

    StateDef(name, blk)
  }

  def portDef(ctx: TP.Port_defContext): ValDef = {
    val modifier = Modifier(ctx.getChild(0).getText)
    val (name, tpe, expr) = componentBody(ctx.component_def_body)

    ValDef(modifier, name, tpe, expr)
  }

  def regDef(ctx: TP.Reg_defContext): ValDef = {
    val (name, tpe, expr) = componentBody(ctx.component_def_body)

    ValDef(Modifier.Register, name, tpe, expr)
  }

  def componentBody(ctx: TP.Component_def_bodyContext): (String, Option[TypeTree], Option[Expression]) = {
    val name = ctx.ID.getText
    val tpe = Option(ctx.`type`).map(typeTree)
    val initExpr = Option(ctx.expr).map(expr)

    (name, tpe, initExpr)
  }

  def expr(ctx: TP.ExprContext): Expression = ctx match {
    case ctx: TP.SelectExprContext => selectExpr(ctx)
    case ctx: TP.MulDivExprContext => binop(ctx.expr(0), ctx.expr(1), ctx.op.getText)
    case ctx: TP.AddSubExprContext => binop(ctx.expr(0), ctx.expr(1), ctx.op.getText)
    case ctx: TP.ApplyExprContext => applyCall(ctx.apply)
    case ctx: TP.BlockExprContext => block(ctx.block)
    case ctx: TP.ConstructExprContext => construct(ctx.construct)
    case ctx: TP.IfExprContext =>
      val cond = expr(ctx.expr)
      val conseq = block(ctx.block(0))
      val alt = Option(ctx.block(1)).map(block)

      IfExpr(cond, conseq, alt)
    case _: TP.FinishContext => Finish()
    case ctx: TP.GotoContext => Goto(ctx.ID.getText)
    case ctx: TP.RelayContext =>
      val args = ctx.args.expr.asScala.map(expr).toVector
      Relay(ctx.ID.getText, args)
    case ctx: TP.GenerateContext =>
      val args = ctx.args.expr.asScala.map(expr).toVector
      Generate(ctx.ID.getText, args)
    case ctx: TP.LitExprContext => literal(ctx.literal)
    case ctx: TP.ParenthesesExprContext => expr(ctx.expr)
    case _: TP.SelfExprContext => Self()
    case ctx: TP.IDContext => Ident(ctx.ID.getText)
  }

  def selectExpr(ctx: TP.SelectExprContext): Expression = Option(ctx.apply) match {
    case Some(applyCtx) =>
      val Apply(Ident(name), hp, tp, args) = applyCall(applyCtx)
      val prefix = expr(ctx.expr)
      Apply(Select(prefix, name), hp, tp, args)
    case None =>
      val prefix = expr(ctx.expr)
      val name = ctx.ID.getText
      Select(prefix, name)
  }

  def binop(left: TP.ExprContext, right: TP.ExprContext, op: String): Apply = {
    val name = op match {
      case "+" => "add"
      case "-" => "sub"
      case "*" => "mul"
      case "/" => "div"
    }

    Apply(Select(expr(left), name), Vector.empty, Vector.empty, Vector(expr(right)))
  }

  def typeTree(ctx: TP.TypeContext): TypeTree = {
    val name = ctx.ID.getText
    val hps = Option(ctx.apply_hardparam).map(applyHardParam).getOrElse(Vector.empty)
    val tps = Option(ctx.apply_typeparam).map(applyTypeParam).getOrElse(Vector.empty)

    TypeTree(name, hps, tps)
  }

  def applyCall(ctx: TP.ApplyContext): Apply = {
    val name = ctx.ID.getText
    val hp = Option(ctx.apply_hardparam).map(applyHardParam).getOrElse(Vector.empty)
    val tp = Option(ctx.apply_typeparam).map(applyTypeParam).getOrElse(Vector.empty)
    val args = ctx.args.expr.asScala.map(expr).toVector

    Apply(Ident(name), hp, tp, args)
  }

  def applyHardParam(ctx: TP.Apply_hardparamContext): Vector[Expression] =
    ctx.expr.asScala.map(expr).toVector

  def applyTypeParam(ctx: TP.Apply_typeparamContext): Vector[TypeTree] =
    ctx.`type`.asScala.map(typeTree).toVector

  def block(ctx: TP.BlockContext): Block = {
    val elems = ctx.block_elem
      .asScala
      .map(blockElem)
      .toVector

    elems match {
      case Vector() => Block(Vector.empty, UnitLiteral())
      case elems => elems.last match {
        case e: Expression => Block(elems.dropRight(1), e)
        case _: ValDef     => Block(elems, UnitLiteral())
      }
    }
  }

  def blockElem(ctx: TP.Block_elemContext): BlockElem = ctx.getChild(0) match {
    case ctx: TP.Val_defContext => valDef(ctx)
    case ctx: TP.ExprContext => expr(ctx)
  }

  def construct(ctx: TP.ConstructContext): Construct = {
    def constructPair(ctx: TP.Construct_pairContext): ConstructPair =
      ConstructPair(ctx.ID.getText, expr(ctx.expr))

    val tpe = typeTree(ctx.`type`)
    val pairs = Option(ctx.construct_pair)
      .map(_.asScala.map(constructPair).toVector)
      .getOrElse(Vector.empty)

    Construct(tpe, pairs)
  }

  def bound(ctx: TP.BoundContext): Bound = {
    val target = ctx.ID.getText
    val constraints = ctx.`type`
      .asScala
      .map(typeTree)
      .toVector

    Bound(target, constraints)
  }

  def literal(ctx: TP.LiteralContext): Expression = ctx match {
    case ctx: TP.BitLitContext =>
      val raw = ctx.BIT.getText.substring(2)
      BitLiteral(BigInt(raw, 2), raw.length)
    case ctx: TP.IntLitContext =>
      ctx.INT.getText.toIntOption match {
        case Some(value) => IntLiteral(value)
        case None => ???
      }
    case ctx: TP.StringLitContext =>
      StringLiteral(ctx.STRING().getText)
    case _: TP.UnitLitContext =>
      UnitLiteral()
  }

  def component(ctx: TP.ComponentContext): Component = ctx.getChild(0) match {
    case ctx: TP.Port_defContext   => portDef(ctx)
    case ctx: TP.Reg_defContext    => regDef(ctx)
    case ctx: TP.Method_defContext => methodDef(ctx)
    case ctx: TP.Stage_defContext  => stageDef(ctx)
    case ctx: TP.Always_defContext => alwaysDef(ctx)
  }

}