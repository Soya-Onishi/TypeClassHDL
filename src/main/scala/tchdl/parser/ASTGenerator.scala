package tchdl.parser

import org.antlr.v4.runtime.tree.TerminalNode
import tchdl.ast._
import tchdl.util.Modifier
import tchdl.antlr.{TchdlParser => TP}
import tchdl.util.TchdlException.ImplementationErrorException

import scala.jdk.CollectionConverters._

class ASTGenerator {
  def apply(ctx: TP.Compilation_unitContext, filename: String): CompilationUnit = {
    val pkgName = ctx.pkg_name.EXPR_ID.asScala.map(_.getText).toVector
    val imports = ctx.import_clause.asScala.map(_.EXPR_ID.asScala.map(_.getText).toVector).toVector
    val defs = ctx.top_definition.asScala.map(topDefinition).toVector

    CompilationUnit(Some(filename), pkgName, imports, defs)
  }

  def topDefinition(ctx: TP.Top_definitionContext): Definition = {
    ctx.getChild(0) match {
      case ctx: TP.Module_defContext => moduleDef(ctx)
      case ctx: TP.Method_defContext => methodDef(ctx)
      case ctx: TP.Struct_defContext => structDef(ctx)
      case ctx: TP.Interface_defContext => interfaceDef(ctx)
      case ctx: TP.Implement_interfaceContext => implementInterface(ctx)
    }
  }

  def moduleDef(ctx: TP.Module_defContext): ModuleDef = {
    def paramModules[T](params: Option[T])(ids: T => java.util.List[TerminalNode])(types: T => java.util.List[TP.TypeContext]): Vector[ValDef] =
      params.map{ ctx =>
        val idents = ids(ctx).asScala.map(_.getText)
        val tpes = types(ctx).asScala.map(typeTree)

        idents zip tpes
      }.map { _.map {
        case (ident, tpe) => ValDef(Modifier.NoModifier, ident, Some(tpe), None)
      }}.getOrElse(Vector.empty).toVector

    val name = ctx.TYPE_ID.getText
    val (hp, tp, bound) = definitionHeader(ctx.type_param(), ctx.bounds())
    val parents = paramModules(Option(ctx.parents))(_.EXPR_ID)(_.`type`)
    val siblings = paramModules(Option(ctx.siblings))(_.EXPR_ID)(_.`type`)

    val components = ctx.component
      .asScala
      .map(component)
      .toVector

    ModuleDef(name, hp, tp, bound, parents, siblings, components)
  }

  def structDef(ctx: TP.Struct_defContext): StructDef = {
    val name = ctx.TYPE_ID.getText
    val (hp, tp, bound) = definitionHeader(ctx.type_param(), ctx.bounds())
    val fields = fieldDefs(ctx.field_defs)

    StructDef(name, hp, tp, bound, fields)
  }

  def implementClass(ctx: TP.Implement_classContext): ImplementClass = {
    val target = typeTree(ctx.`type`())
    val (hps, tps) = Option(ctx.type_param).map(typeParam).getOrElse((Vector.empty, Vector.empty))
    val bounds = Option(ctx.bounds).map(_.bound.asScala.map(bound).toVector).getOrElse(Vector.empty)
    val methods = ctx.method_def.asScala.map(methodDef).toVector
    val stages = ctx.stage_def.asScala.map(stageDef).toVector

    ImplementClass(target, hps, tps, bounds, methods, stages)
  }

  def interfaceDef(ctx: TP.Interface_defContext): InterfaceDef = {
    val name = ctx.TYPE_ID.getText
    val (hp, tp, bound) = definitionHeader(ctx.type_param(), ctx.bounds())
    val methods = ctx.signature_def
      .asScala
      .map(signatureDef)
      .toVector

    InterfaceDef(name, hp, tp, bound, methods)
  }

  def implementInterface(ctx: TP.Implement_interfaceContext): ImplementInterface = {
    val (hp, tp, bound) = definitionHeader(ctx.type_param(), ctx.bounds())
    val Seq(targetTrait, tpe) = ctx.`type`().asScala.map(typeTree).toSeq
    val methods = ctx.method_def.asScala.map(methodDef).toVector

    ImplementInterface(targetTrait, tpe, hp, tp, bound, methods)
  }

  def methodDef(ctx: TP.Method_defContext): MethodDef = {
    val name = ctx.EXPR_ID.getText
    val (hps, tps, bounds) = definitionHeader(ctx.type_param(), ctx.bounds())
    val params = Option(ctx.param_defs())
      .map(paramDefs)
      .getOrElse(Vector.empty)
    val tpe = typeTree(ctx.`type`)
    val blk = block(ctx.block)

    MethodDef(name, hps, tps, bounds, params, tpe, Some(blk))
  }

  def signatureDef(ctx: TP.Signature_defContext): MethodDef = {
    val name = ctx.EXPR_ID.getText
    val (hps, tps, bounds) = definitionHeader(ctx.type_param(), ctx.bounds())
    val params = Option(ctx.param_defs())
      .map(paramDefs)
      .getOrElse(Vector.empty)
    val tpe = typeTree(ctx.`type`)

    MethodDef(name, hps, tps, bounds, params, tpe, None)
  }

  def definitionHeader(tpCtx: TP.Type_paramContext, boundsCtx: TP.BoundsContext): (Vector[ValDef], Vector[TypeDef], Vector[BoundTree]) = {
    val (hps, tps) = Option(tpCtx)
      .map(typeParam)
      .getOrElse(Vector.empty, Vector.empty)

    val bounds = Option(boundsCtx)
      .map(
        _.bound
          .asScala
          .map(bound)
          .toVector
      ).getOrElse(Vector.empty)

    (hps, tps, bounds)
  }

  def fieldDefs(ctx: TP.Field_defsContext): Vector[ValDef] =
    Option(ctx.field_def)
      .map(_.asScala.map(fieldDef).toVector)
      .getOrElse(Vector.empty)

  def fieldDef(ctx: TP.Field_defContext): ValDef = {
    val modifier = Modifier(ctx.modifier
      .asScala
      .map(_.getChild(0).getText)
      .toVector
    )

    val name = ctx.EXPR_ID.getText
    val tpe = typeTree(ctx.`type`())

    ValDef(modifier | Modifier.NoExpr, name, Some(tpe), None)
  }

  def paramDefs(ctx: TP.Param_defsContext): Vector[ValDef] = {
    Option(ctx.param_def)
      .map(_.asScala.map(paramDef).toVector)
      .getOrElse(Vector.empty)
  }

  def paramDef(ctx: TP.Param_defContext): ValDef = {
    val modifier = Modifier(ctx.modifier
      .asScala
      .map(_.getChild(0).getText)
      .toVector
    )

    val name = ctx.EXPR_ID.getText
    val tpe = typeTree(ctx.`type`())

    ValDef(modifier | Modifier.NoExpr, name, Some(tpe), None)
  }

  def alwaysDef(ctx: TP.Always_defContext): AlwaysDef = {
    val name = ctx.EXPR_ID.getText
    val blk = block(ctx.block)

    AlwaysDef(name, blk)
  }

  def valDef(ctx: TP.Val_defContext): ValDef = {
    val name = ctx.EXPR_ID.getText
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

    val name = ctx.EXPR_ID.getText
    val params = Option(ctx.param_defs)
      .map(paramDefs)
      .getOrElse(Vector.empty)
    val tpe = typeTree(ctx.`type`)
    val (states, blks) =
      Option(ctx.stage_body)
        .map(stageBody)
        .getOrElse((Vector.empty, Vector.empty))

    StageDef(name, params, tpe, states, blks)
  }

  def stateDef(ctx: TP.State_defContext): StateDef = {
    val name = ctx.EXPR_ID.getText
    val blk = block(ctx.block)

    StateDef(name, blk)
  }

  def portDef(ctx: TP.Port_defContext): ValDef = {
    val modifier = Modifier(ctx.getChild(0).getText)
    val (name, tpe, expr) = componentBody(ctx.component_def_body)

    ValDef(modifier, name, tpe, expr)
  }

  def submoduleDef(ctx: TP.Submodule_defContext): ValDef = {
    val (name, tpe, expr) = componentBody(ctx.component_def_body)
    ValDef(Modifier.NoModifier, name, tpe, expr)
  }

  def regDef(ctx: TP.Reg_defContext): ValDef = {
    val (name, tpe, expr) = componentBody(ctx.component_def_body)
    ValDef(Modifier.Register, name, tpe, expr)
  }

  def componentBody(ctx: TP.Component_def_bodyContext): (String, Option[TypeTree], Option[Expression]) = {
    val name = ctx.EXPR_ID.getText
    val tpe = Option(ctx.`type`).map(typeTree)
    val initExpr = Option(ctx.expr).map(expr)

    (name, tpe, initExpr)
  }

  def expr(ctx: TP.ExprContext): Expression = ctx match {
    case ctx: TP.SelectExprContext => selectExpr(ctx)
    case ctx: TP.MulDivExprContext => stdBinOp(ctx.expr(0), ctx.expr(1), ctx.op.getText)
    case ctx: TP.AddSubExprContext => stdBinOp(ctx.expr(0), ctx.expr(1), ctx.op.getText)
    case ctx: TP.ApplyExprContext => applyCall(ctx.apply)
    case ctx: TP.BlockExprContext => block(ctx.block)
    case ctx: TP.ConstructExprContext => construct(ctx.construct)
    case ctx: TP.IfExprContext =>
      val cond = expr(ctx.expr)
      val conseq = block(ctx.block(0))
      val alt = Option(ctx.block(1)).map(block)

      IfExpr(cond, conseq, alt)
    case _: TP.FinishContext => Finish()
    case ctx: TP.GotoContext => Goto(ctx.EXPR_ID.getText)
    case ctx: TP.RelayContext =>
      val args = ctx.args.expr.asScala.map(expr).toVector
      Relay(ctx.EXPR_ID.getText, args)
    case ctx: TP.GenerateContext =>
      val args = ctx.args.expr.asScala.map(expr).toVector
      Generate(ctx.EXPR_ID.getText, args)
    case ctx: TP.LitExprContext => literal(ctx.literal)
    case ctx: TP.ParenthesesExprContext => expr(ctx.expr)
    case _: TP.SelfExprContext => Self()
    case ctx: TP.ExprIDContext => Ident(ctx.EXPR_ID.getText)
  }

  def hpExpr(ctx: TP.Hp_exprContext): HPExpr = ctx match {
    case ctx: TP.MulDivHPExprContext => hpBinOp(ctx.hp_expr(0), ctx.hp_expr(1), ctx.op.getText)
    case ctx: TP.AddSubHPExprContext => hpBinOp(ctx.hp_expr(0), ctx.hp_expr(1), ctx.op.getText)
    case ctx: TP.StrLitHPExprContext => StringLiteral(ctx.STRING.getText.tail.init)
    case ctx: TP.IntLitHPExprContext => IntLiteral(ctx.INT.getText.toInt)
    case ctx: TP.HPExprIDContext => Ident(ctx.getText)
  }

  def selectExpr(ctx: TP.SelectExprContext): Expression = Option(ctx.apply) match {
    case Some(applyCtx) =>
      val prefix = expr(ctx.expr)

      applyCall(applyCtx) match {
        case ApplyParams(Ident(name), args) =>
          ApplyParams(Select(prefix, name), args)
        case ApplyParams(ApplyTypeParams(Ident(name), tps, hps), args) =>
          ApplyParams(ApplyTypeParams(Select(prefix, name), tps, hps), args)
        case ApplyParams(expr, _) =>
          val msg = s"${expr.getClass} must not appear here"
          throw new ImplementationErrorException(msg)
      }
    case None =>
      val prefix = expr(ctx.expr)
      val name = ctx.EXPR_ID.getText
      Select(prefix, name)
  }

  def stdBinOp(left: TP.ExprContext, right: TP.ExprContext, op: String): StdBinOp = {
    val operation = op match {
      case "+" => Operation.Add
      case "-" => Operation.Sub
      case "*" => Operation.Mul
      case "/" => Operation.Div
    }

    StdBinOp(operation, expr(left), expr(right))
  }

  def hpBinOp(left: TP.Hp_exprContext, right: TP.Hp_exprContext, op: String): HPBinOp = {
    val operation = op match {
      case "+" => Operation.Add
      case "-" => Operation.Sub
      case "*" => Operation.Mul
      case "/" => Operation.Div
    }

    HPBinOp(operation, hpExpr(left), hpExpr(right))
  }

  def typeTree(ctx: TP.TypeContext): TypeTree = {
    ctx match {
      case ctx: TP.NormalTypeContext =>
        val id = Ident(ctx.TYPE_ID.getText)
        Option(ctx.apply_typeparam).map(applyTypeParam) match {
          case Some((hps, tps)) => TypeTree(id, hps, tps)
          case None => TypeTree(id, Vector.empty, Vector.empty)
        }
    }
  }

  def applyCall(ctx: TP.ApplyContext): ApplyParams = {
    val name = ctx.EXPR_ID.getText
    val tpsOpt = Option(ctx.apply_typeparam).map(applyTypeParam)
    val args = ctx.args.expr.asScala.map(expr).toVector

    tpsOpt match {
      case Some((hps, tps)) => ApplyParams(ApplyTypeParams(Ident(name), hps, tps), args)
      case None => ApplyParams(Ident(name), args)
    }
  }

  def typeParam(ctx: TP.Type_paramContext): (Vector[ValDef], Vector[TypeDef]) = {
    ctx match {
      case ctx: TP.WithDependencyContext =>
        val deps = paramDefs(ctx.param_defs)
        val tps = ctx.TYPE_ID()
          .asScala
          .map(_.getText)
          .map(TypeDef.apply)
          .toVector

        (deps, tps)
      case ctx: TP.WithoutDependencyContext =>
        val tps = ctx.TYPE_ID()
          .asScala
          .map(_.getText)
          .map(TypeDef.apply)
          .toVector

        (Vector.empty, tps)
    }
  }

  def applyTypeParam(ctx: TP.Apply_typeparamContext): (Vector[HPExpr], Vector[TypeTree]) = ctx match {
    case ctx: TP.WithHardwareParamsContext =>
      val exprs = hardwareParams(ctx.hardware_params)
      val tpes = Option(ctx.type_params).map(typeParams).getOrElse(Vector.empty)

      (exprs, tpes)
    case ctx: TP.WithoutHardwareParamsContext =>
      val tpes = typeParams(ctx.type_params)

      (Vector.empty, tpes)
  }

  def hardwareParams(ctx: TP.Hardware_paramsContext): Vector[HPExpr] =
    ctx.hp_expr.asScala.map(hpExpr).toVector

  def typeParams(ctx: TP.Type_paramsContext): Vector[TypeTree] =
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
      ConstructPair(ctx.EXPR_ID.getText, expr(ctx.expr))

    val tpe = typeTree(ctx.`type`)
    val pairs = Option(ctx.construct_pair)
      .map(_.asScala.map(constructPair).toVector)
      .getOrElse(Vector.empty)

    Construct(tpe, pairs)
  }

  def bound(ctx: TP.BoundContext): BoundTree = {
    def hpBoundExpr(ctx: TP.Hp_bound_exprContext): RangeExpr = ctx match {
      case ctx: TP.MaxBoundContext => RangeExpr.Max(hpExpr(ctx.hp_expr))
      case ctx: TP.MinBoundContext => RangeExpr.Min(hpExpr(ctx.hp_expr))
      case ctx: TP.EqBoundContext => RangeExpr.EQ(hpExpr(ctx.hp_expr))
      case ctx: TP.NeBoundContext => RangeExpr.NE(hpExpr(ctx.hp_expr))
    }

    ctx match {
      case ctx: TP.TPBoundContext =>
        val target = TypeTree(Ident(ctx.TYPE_ID.getText), Vector.empty, Vector.empty)
        val bounds = ctx.`type`.asScala.map(typeTree)

        TPBoundTree(target, bounds.toVector)
      case ctx: TP.HPBoundContext =>
        val target = hpExpr(ctx.hp_expr)
        val bounds = ctx.hp_bound_expr.asScala.map(hpBoundExpr).toVector

        HPBoundTree(target, bounds)
    }
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
    case ctx: TP.Submodule_defContext => submoduleDef(ctx)
    case ctx: TP.Reg_defContext    => regDef(ctx)
    case ctx: TP.Method_defContext => methodDef(ctx)
    case ctx: TP.Stage_defContext  => stageDef(ctx)
    case ctx: TP.Always_defContext => alwaysDef(ctx)
  }

}
