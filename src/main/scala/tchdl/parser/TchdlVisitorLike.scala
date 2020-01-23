package tchdl.parser

import org.antlr.v4.runtime.ParserRuleContext
import tchdl.ast._
import tchdl.util.Modifier
import tchdl.antlr._

import scala.jdk.CollectionConverters._

class TchdlVisitorLike(val filename: Option[String]) extends TchdlBaseVisitor[AST] {
  def visitCompilationUnit(ctx: TchdlParser.Compilation_unitContext): CompilationUnit = {
    val defs = ctx
      .top_definition
      .asScala
      .map(visit(_).asInstanceOf[AST with Definition])
      .toArray

    CompilationUnit(filename, defs)
  }

  override def visitClass_def(ctx: TchdlParser.Class_defContext): ClassDef = {
    val name = ctx.ID.getText
    val hp = getHardwareParam(ctx.hardware_param())
    val tp = getTypeParam(ctx.type_param())
    val bounds = getBounds(ctx.bounds())

    val methods = ctx
      .method_def
      .asScala
      .map(visit(_))
      .toArray
      .map(_.asInstanceOf[MethodDef])

    ClassDef(name, hp, tp, bounds, methods)
  }

  override def visitInterface_def(ctx: TchdlParser.Interface_defContext): InterfaceDef = {
    val name = ctx.ID().getText
    val hp = getHardwareParam(ctx.hardware_param())
    val tp = getTypeParam(ctx.type_param())
    val bounds = getBounds(ctx.bounds())

    val interfaces = ctx.children
      .asScala
      .collect{
        case m: TchdlParser.Method_defContext => visitMethod_def(m)
        case s: TchdlParser.Stage_defContext => visitStage_def(s)
      }
      .map{ c: Component => c }
      .toArray

    InterfaceDef(name, hp, tp, bounds, interfaces)
  }

  override def visitImplement(ctx: TchdlParser.ImplementContext): Implement = {
    val hp = getHardwareParam(ctx.hardware_param())
    val tp = getTypeParam(ctx.type_param())
    val bounds = getBounds(ctx.bounds())
    val tpe = visitType(ctx.`type`(0))
    val target = visitType(ctx.`type`(1))
    val inners = ctx.children
      .asScala
      .collect{
        case m: TchdlParser.Method_defContext => visitMethod_def(m)
        case s: TchdlParser.Stage_defContext => visitStage_def(s)
      }
      .map{ c: Component => c }
      .toArray

    Implement(tpe, target, hp, tp, bounds, inners)
  }

  def visitFieldDefs(ctx: TchdlParser.Field_defsContext): Array[FieldDef] =
    Option(ctx.field_def)
      .map(_.asScala.toArray)
      .getOrElse(Array.empty[TchdlParser.Field_defContext])
      .map(visitField_def(_))

  override def visitModule_def(ctx: TchdlParser.Module_defContext): ModuleDef = {
    val name = ctx.ID().getText
    val hp = getHardwareParam(ctx.hardware_param())
    val tp = getTypeParam(ctx.type_param())
    val bounds = getBounds(ctx.bounds())
    val passedModules = visitFieldDefs(ctx.field_defs())
    val components = ctx.component()
      .asScala
      .map(visitComponent(_))
      .toArray

    ModuleDef(name, hp, tp, bounds, passedModules, components)
  }

  override def visitComponent(ctx: TchdlParser.ComponentContext): Component =
    super.visitComponent(ctx).asInstanceOf[Component]

  override def visitStruct_def(ctx: TchdlParser.Struct_defContext): StructDef = {
    val name = ctx.ID().getText
    val hp = getHardwareParam(ctx.hardware_param())
    val tp = getTypeParam(ctx.type_param())
    val bounds = getBounds(ctx.bounds())
    val fields = visitFieldDefs(ctx.field_defs())

    StructDef(name, hp, tp, bounds, fields)
  }

  override def visitField_def(ctx: TchdlParser.Field_defContext): FieldDef = {
    val modifier = Modifier(
      Option(ctx.modifier)
        .map(_.asScala.toArray)
        .getOrElse(Array.empty[TchdlParser.ModifierContext])
        .map(_.getChild(0).getText)
    )

    val name = ctx.ID().getText
    val tpe = visitType(ctx.`type`())

    FieldDef(modifier, name, tpe)
  }

  override def visitEnum_def(ctx: TchdlParser.Enum_defContext): EnumDef = {
    val name = ctx.ID().getText
    val hp = getHardwareParam(ctx.hardware_param())
    val tp = getTypeParam(ctx.type_param())
    val bounds = getBounds(ctx.bounds())
    val fields = ctx.enum_field_def()
      .asScala
      .map(visitEnum_field_def(_))
      .toArray

    EnumDef(name, hp, tp, bounds, fields)
  }

  override def visitEnum_field_def(ctx: TchdlParser.Enum_field_defContext): EnumFieldDef = {
    val name = ctx.ID().getText
    val tpes = ctx.`type`()
      .asScala
      .map(visitType(_))
      .toArray

    EnumFieldDef(name, tpes)
  }

  override def visitAlways_def(ctx: TchdlParser.Always_defContext): AlwaysDef = {
    val name = ctx.ID().getText
    val blk = visitBlock(ctx.block())

    AlwaysDef(name, blk)
  }

  override def visitMethod_def(ctx: TchdlParser.Method_defContext): MethodDef = {
    val name = ctx.ID().getText
    val hp = getHardwareParam(ctx.hardware_param())
    val tp = getTypeParam(ctx.type_param())
    val bounds = getBounds(ctx.bounds())
    val params = visitFieldDefs(ctx.field_defs())
    val retTpe = visitType(ctx.`type`())
    val blk = Option(ctx.block()).map(visitBlock)

    MethodDef(name, hp, tp, bounds, params, retTpe, blk)
  }

  override def visitVal_def(ctx: TchdlParser.Val_defContext): ValDef = {
    val name = ctx.ID().getText
    val tpe = Option(ctx.`type`()).map(visitType)
    val expr = visitExpr(ctx.expr())

    ValDef(Modifier.NoModifier, name, tpe, Some(expr))
  }

  override def visitStage_def(ctx: TchdlParser.Stage_defContext): StageDef = {
    val name = ctx.ID().getText
    val params = visitFieldDefs(ctx.field_defs())
    val retTpe = visitType(ctx.`type`())
    val (states, blockElems) = visitStageBody(ctx.stage_body())

    StageDef(name, params, retTpe, states, blockElems)
  }

  def visitStageBody(ctx: TchdlParser.Stage_bodyContext): (Array[StateDef], Array[BlockElem]) = {
    val state = ctx.state_def()
      .asScala
      .map(visitState_def(_))
      .toArray

    val blkElem = ctx.block_elem()
      .asScala
      .map(visitBlock_elem(_))
      .toArray

    (state, blkElem)
  }

  override def visitState_def(ctx: TchdlParser.State_defContext): StateDef = {
    val name = ctx.ID().getText
    val blk = visitBlock(ctx.block())

    StateDef(name, blk)
  }

  override def visitPort_def(ctx: TchdlParser.Port_defContext): ValDef = {
    val modifier = ctx.getChild(0).getText match {
      case "input" => Modifier.Input
      case "internal" => Modifier.Internal
      case "output" => Modifier.Output
    }

    val (name, tpe, expr) = visitComponentDefBody(ctx.component_def_body)

    ValDef(modifier, name, tpe, expr)
  }

  override def visitReg_def(ctx: TchdlParser.Reg_defContext): ValDef = {
    val modifier = Modifier.Register
    val (name, tpe, expr) = visitComponentDefBody(ctx.component_def_body)

    ValDef(modifier, name, tpe, expr)
  }

  def visitComponentDefBody(ctx: TchdlParser.Component_def_bodyContext): (String, Option[TypeTree], Option[Expression]) = {
    val name = ctx.ID.getText
    val tpe = Option(ctx.`type`).map(visitType)
    val expr = Option(ctx.expr).map(visitExpr)

    (name, tpe, expr)
  }

  def visitTypeBounds(ctx: TchdlParser.BoundsContext): Array[Bound] =
    ctx.bound.asScala.map(visitBound).toArray

  override def visitBound(ctx: TchdlParser.BoundContext): Bound = {
    val name = ctx.ID().getText
    val constraints = ctx.`type`()
      .asScala
      .map(visitType(_))
      .toArray

    Bound(name, constraints)
  }

  override def visitComponent_def_body(ctx: TchdlParser.Component_def_bodyContext): WorkingAST.ComponentBody = {
    val name = ctx.ID().getText

    val tpe = Option(ctx.`type`())
      .map(visitType(_))

    val expr = Option(ctx.expr())
      .map(visit(_))
      .map(_.asInstanceOf[Expression])

    WorkingAST.ComponentBody(name, tpe, expr)
  }

  def visitExpr(ctx: TchdlParser.ExprContext): Expression =
    visit(ctx).asInstanceOf[Expression]

  override def visitSelectExpr(ctx: TchdlParser.SelectExprContext): Expression = {
    val expr = visitExpr(ctx.expr())
    (Option(ctx.apply()), Option(ctx.ID())) match {
      case (Some(apply), None) =>
        val Apply(Ident(name), hp, tp, args) = visitApply(apply)
        val select = Select(expr, name)
        Apply(select, hp, tp, args)
      case (None, Some(id)) =>
        Select(expr, id.getText)
    }
  }

  override def visitAddSubExpr(ctx: TchdlParser.AddSubExprContext): Expression = {
    val left = visitExpr(ctx.expr(0))
    val right = visitExpr(ctx.expr(1))
    val op = ctx.op.getText match {
      case "+" => "add"
      case "-" => "sub"
    }

    Apply(Select(left, op), Array.empty, Array.empty, Array(right))
  }

  override def visitApplyExpr(ctx: TchdlParser.ApplyExprContext): Apply =
    visitApply(ctx.apply())

  override def visitBlockExpr(ctx: TchdlParser.BlockExprContext): Block =
    visitBlock(ctx.block())

  override def visitConstructExpr(ctx: TchdlParser.ConstructExprContext): Construct =
    visitConstruct(ctx.construct())

  override def visitSelfExpr(ctx: TchdlParser.SelfExprContext): Self = Self()

  override def visitIfExpr(ctx: TchdlParser.IfExprContext): IfExpr =
    visitIf_expr(ctx.if_expr())

  override def visitMatchExpr(ctx: TchdlParser.MatchExprContext): Match =
    visitMatch_expr(ctx.match_expr())

  override def visitStageManExpr(ctx: TchdlParser.StageManExprContext): Expression =
    visitStage_man(ctx.stage_man())

  override def visitLitExpr(ctx: TchdlParser.LitExprContext): Expression =
    visitLiteral(ctx.literal())

  override def visitID(ctx: TchdlParser.IDContext): Ident =
    Ident(ctx.ID().getText)

  override def visitApply(ctx: TchdlParser.ApplyContext): Apply = {
    val name = ctx.ID().getText
    val hp = Option(ctx.apply_hardparam())
      .map { ctx =>
        ctx.expr()
          .asScala
          .map(visitExpr(_))
          .toArray
      }
      .getOrElse(Array.empty[Expression])

    val tp = Option(ctx.apply_typeparam())
      .map { ctx =>
        ctx.`type`()
          .asScala
          .map(visitType(_))
          .toArray
      }
      .getOrElse(Array.empty[TypeTree])

    val args = ctx.args()
      .expr()
      .asScala
      .map(visitExpr(_))
      .toArray

    Apply(Ident(name), hp, tp, args)
  }

  override def visitBlock(ctx: TchdlParser.BlockContext): Block = {
    val blkElems = ctx.block_elem()
      .asScala
      .map(visitBlock_elem(_))
      .toArray

    val (elems, last) = blkElems.lastOption match {
      case None => (Array.empty[BlockElem], UnitLiteral())
      case Some(last) => last match {
        case _: ValDef => (blkElems, UnitLiteral())
        case expr: Expression => (blkElems.dropRight(1), expr)
      }
    }

    Block(elems, last)
  }


  override def visitBlock_elem(ctx: TchdlParser.Block_elemContext): BlockElem = {
    (Option(ctx.val_def()), Option(ctx.expr())) match {
      case (Some(vdef), None) => visitVal_def(vdef)
      case (None, Some(expr)) => visitExpr(expr)
    }
  }

  override def visitConstruct(ctx: TchdlParser.ConstructContext): Construct = {
    val tpe = visitType(ctx.`type`())
    val cp = ctx.construct_pairs()
      .construct_pair()
      .asScala
      .map{ pair =>
        val id = pair.ID().getText
        val expr = visitExpr(pair.expr())

        ConstructPair(id, expr)
      }
      .toArray

    Construct(tpe, cp)
  }

  override def visitIf_expr(ctx: TchdlParser.If_exprContext): IfExpr = {
    val cond = visitExpr(ctx.expr())
    val conseq = visitBlock(ctx.block(0))
    val alt = Option(ctx.block(1)).map(visitBlock(_))

    IfExpr(cond, conseq, alt)
  }

  override def visitMatch_expr(ctx: TchdlParser.Match_exprContext): Match = {
    val expr = visitExpr(ctx.expr())
    val cases = ctx.case_def()
      .asScala
      .map { cd =>
        val lit = visitLiteral(cd.literal())
        val exprs = cd.block_elem()
          .asScala
          .map(visitBlock_elem(_))
          .toArray

        val blk = exprs.lastOption match {
          case None => Block(Array.empty[BlockElem], UnitLiteral())
          case Some(last) => last match {
            case _: ValDef => Block(exprs, UnitLiteral())
            case expr: Expression => Block(exprs.dropRight(1), expr)
          }
        }

        Case(lit, blk)
      }
      .toArray

    Match(expr, cases)
  }

  override def visitStage_man(ctx: TchdlParser.Stage_manContext): Expression = {
    def makeTree[T](
       constructor: (String, Array[Expression]) => T): T =
    {
      val target = ctx.ID().getText
      val args = ctx.args()
        .expr()
        .asScala
        .map(visitExpr(_))
        .toArray

      constructor(target, args)
    }

    ctx.getChild(0).getText match {
      case "finish" => Finish()
      case "goto" => Goto(ctx.ID().getText)
      case "relay" => makeTree(Relay.apply)
      case "generate" => makeTree(Generate.apply)
    }
  }

  override def visitLiteral(ctx: TchdlParser.LiteralContext): Expression = {
    (Option(ctx.BIT()), Option(ctx.INT()), Option(ctx.unit_lit()), Option(ctx.STRING())) match {
      case (Some(bit), _, _, _) =>
        val literal = bit.getText.substring(2)
        val length = literal.length
        val value = BigInt(literal, 2)

        BitLiteral(value, length)
      case (_, Some(int), _, _) => int.getText match {
        case value if value.contains("0x") =>
          IntLiteral(Integer.parseInt(value.substring(2), 16))
        case value =>
          IntLiteral(Integer.parseInt(value))
      }
      case (_, _, Some(_), _) =>
        UnitLiteral()
      case (_, _, _, Some(str)) =>
        StringLiteral(str.getText)
    }
  }

  def visitTypeParam(ctx: TchdlParser.Type_paramContext): Array[TypeDef] =
    ctx.ID()
      .asScala
      .map(id => TypeDef(id.getText))
      .toArray

  def visitHardwareParam(ctx: TchdlParser.Hardware_paramContext): Array[FieldDef] =
    ctx.field_defs()
      .field_def()
      .asScala
      .map(visitField_def(_))
      .toArray

  override def visitType(ctx: TchdlParser.TypeContext): TypeTree = {
    val name = ctx.ID().getText
    val hps = Option(ctx.expr())
      .map { ctx =>
        ctx.asScala
          .map(visitExpr(_))
          .toArray
      }
      .getOrElse(Array.empty[Expression])

    val tps = Option(ctx.`type`())
      .map { ctx =>
        ctx.asScala
          .map(visitType(_))
          .toArray
      }
      .getOrElse(Array.empty[TypeTree])

    TypeTree(name, hps, tps)
  }

  def getHardwareParam(ctx: TchdlParser.Hardware_paramContext): Array[FieldDef] = {
    Option(visit(ctx))
      .map(_.asInstanceOf[WorkingAST.HardwareParam])
      .map(_.hp)
      .getOrElse(Array())
  }

  def getTypeParam(ctx: TchdlParser.Type_paramContext): Array[TypeDef] = {
    Option(visitType_param(ctx))
      .map(_.asInstanceOf[WorkingAST.TypeParam])
      .map(_.tp)
      .getOrElse(Array())
  }

  def getBounds(ctx: TchdlParser.BoundsContext): Array[Bound] =
    Option(visitTypeBounds(ctx)).getOrElse(Array())

}
