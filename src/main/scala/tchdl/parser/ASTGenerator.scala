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

    val imports = ctx.import_clause
      .asScala
      .map(ctx => ctx.EXPR_ID.asScala.map(_.getText).toVector :+ ctx.TYPE_ID.getText)
      .toVector

    val defs = ctx.top_definition.asScala.map(topDefinition).toVector

    CompilationUnit(Some(filename), pkgName, imports, defs)
  }

  def topDefinition(ctx: TP.Top_definitionContext): Definition = {
    ctx.getChild(0) match {
      case ctx: TP.Module_defContext => moduleDef(ctx)
      case ctx: TP.Method_defContext => methodDef(ctx)
      case ctx: TP.Struct_defContext => structDef(ctx)
      case ctx: TP.Trait_defContext => traitDef(ctx)
      case ctx: TP.Interface_defContext => interfaceDef(ctx)
      case ctx: TP.Implement_classContext => implementClass(ctx)
      case ctx: TP.Implement_interfaceContext => implementInterface(ctx)
    }
  }

  def moduleDef(ctx: TP.Module_defContext): ModuleDef = {
    def paramModules[T](params: Option[T], mod: Modifier)(ids: T => java.util.List[TerminalNode])(types: T => java.util.List[TP.TypeContext]): Vector[ValDef] =
      params.map{ ctx =>
        val idents = ids(ctx).asScala.map(_.getText)
        val tpes = types(ctx).asScala.map(typeTree)

        idents zip tpes
      }.map { _.map {
        case (ident, tpe) => ValDef(mod, ident, Some(tpe), None)
      }}.getOrElse(Vector.empty).toVector

    val name = ctx.TYPE_ID.getText
    val (hp, tp, bound) = definitionHeader(ctx.type_param(), ctx.bounds())

    val parents = paramModules(Option(ctx.parents), Modifier.Parent)(_.EXPR_ID)(_.`type`)
      .map(vdef => vdef.copy(flag = vdef.flag | Modifier.Parent))

    val siblings = paramModules(Option(ctx.siblings), Modifier.Sibling)(_.EXPR_ID)(_.`type`)
      .map(vdef => vdef.copy(flag = vdef.flag | Modifier.Sibling))

    ModuleDef(name, hp, tp, bound, parents, siblings)
  }

  def structDef(ctx: TP.Struct_defContext): StructDef = {
    val name = ctx.TYPE_ID.getText
    val (hp, tp, bound) = definitionHeader(ctx.type_param(), ctx.bounds())
    val fields = Option(ctx.field_defs).map(fieldDefs).getOrElse(Vector.empty)

    StructDef(name, hp, tp, bound, fields)
  }

  def implementClass(ctx: TP.Implement_classContext): ImplementClass = {
    val target = typeTree(ctx.`type`())
    val (hps, tps) = Option(ctx.type_param).map(polyParam).getOrElse((Vector.empty, Vector.empty))
    val bounds = Option(ctx.bounds).map(_.bound.asScala.map(bound).toVector).getOrElse(Vector.empty)
    val components = ctx.component.asScala.map(component).toVector

    ImplementClass(target, hps, tps, bounds, components)
  }

  def traitDef(ctx: TP.Trait_defContext): InterfaceDef = {
    val name = ctx.TYPE_ID.getText
    val (hp, tp, bound) = definitionHeader(ctx.type_param, ctx.bounds)
    val methods = ctx.signature_def
      .asScala
      .map(signatureDef)
      .toVector

    InterfaceDef(Modifier.Trait, name, hp, tp, bound, methods)
  }

  def interfaceDef(ctx: TP.Interface_defContext): InterfaceDef = {
    val name = ctx.TYPE_ID.getText
    val (hp, tp, bound) = definitionHeader(ctx.type_param, ctx.bounds)
    val methods = ctx.signature_def
      .asScala
      .map(signatureDef)
      .toVector

    InterfaceDef(Modifier.Interface, name, hp, tp, bound, methods)
  }

  def implementInterface(ctx: TP.Implement_interfaceContext): ImplementInterface = {
    val (hp, tp, bound) = definitionHeader(ctx.type_param(), ctx.bounds())
    val Seq(targetTrait, tpe) = ctx.`type`().asScala.map(typeTree).toSeq
    val methods = ctx.method_def.asScala.map(methodDef).toVector

    ImplementInterface(targetTrait, tpe, hp, tp, bound, methods)
  }

  def methodDef(ctx: TP.Method_defContext): MethodDef = {
    val modifier = ctx.method_accessor.asScala
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
    val blk = block(ctx.block)

    MethodDef(modifier, name, hps, tps, bounds, params, tpe, Some(blk))
  }

  def signatureDef(ctx: TP.Signature_defContext): MethodDef = {
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

    MethodDef(modifier, name, hps, tps, bounds, params, tpe, None)
  }

  def definitionHeader(tpCtx: TP.Type_paramContext, boundsCtx: TP.BoundsContext): (Vector[ValDef], Vector[TypeDef], Vector[BoundTree]) = {
    val (hps, tps) = Option(tpCtx)
      .map(polyParam)
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
    ctx.field_def.asScala.map(fieldDef).toVector

  def fieldDef(ctx: TP.Field_defContext): ValDef = {
    val name = ctx.EXPR_ID.getText
    val tpe = typeTree(ctx.`type`())

    ValDef(Modifier.NoModifier, name, Some(tpe), None)
  }

  def paramDefs(ctx: TP.Param_defsContext): Vector[ValDef] = {
    Option(ctx.param_def)
      .map(_.asScala.map(paramDef).toVector)
      .getOrElse(Vector.empty)
  }

  def paramDef(ctx: TP.Param_defContext): ValDef = {
    val name = ctx.EXPR_ID.getText
    val tpe = typeTree(ctx.`type`())

    ValDef(Modifier.NoModifier, name, Some(tpe), None)
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
    val modifier = Modifier(ctx.modifier.getText)
    val name = ctx.EXPR_ID.getText
    val tpe = typeTree(ctx.`type`)

    ValDef(modifier, name, Some(tpe), None)
  }

  def submoduleDef(ctx: TP.Submodule_defContext): ValDef = {
    val (name, tpe, expr) = componentBody(ctx.component_def_body)
    ValDef(Modifier.Child, name, tpe, Some(expr))
  }

  def regDef(ctx: TP.Reg_defContext): ValDef = {
    val (name, tpe, expr) = componentBody(ctx.component_def_body)
    ValDef(Modifier.Register, name, tpe, Some(expr))
  }

  def componentBody(ctx: TP.Component_def_bodyContext): (String, Option[TypeTree], Expression) = {
    val name = ctx.EXPR_ID.getText
    val tpe = Option(ctx.`type`).map(typeTree)
    val initExpr = expr(ctx.expr)

    (name, tpe, initExpr)
  }

  def expr(ctx: TP.ExprContext): Expression = ctx match {
    case ctx: TP.SelectExprContext => selectExpr(ctx)
    case ctx: TP.MulDivExprContext => stdBinOp(ctx.expr(0), ctx.expr(1), ctx.op.getText)
    case ctx: TP.AddSubExprContext => stdBinOp(ctx.expr(0), ctx.expr(1), ctx.op.getText)
    case ctx: TP.ApplyExprContext => applyCall(ctx.apply)
    case ctx: TP.BlockExprContext => block(ctx.block)
    case ctx: TP.ConstructStructExprContext => constructStruct(ctx.construct_struct)
    case ctx: TP.ConstructModuleExprContext => constructModule(ctx.construct_module)
    case ctx: TP.IfExprContext =>
      val cond = expr(ctx.expr(0))
      val conseq = expr(ctx.expr(1))
      val alt = Option(ctx.expr(2)).map(expr)

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
    case _: TP.SelfExprContext => This()
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
        case Apply(Ident(name), hps, tps, args) =>
          Apply(Select(prefix, name), hps, tps, args)
        case Apply(expr, _, _, _) =>
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

  def applyCall(ctx: TP.ApplyContext): Apply = {
    val name = ctx.EXPR_ID.getText
    val tpsOpt = Option(ctx.apply_typeparam).map(applyTypeParam)
    val args = ctx.args.expr.asScala.map(expr).toVector

    tpsOpt match {
      case Some((hps, tps)) => Apply(Ident(name), hps, tps, args)
      case None => Apply(Ident(name), Vector.empty, Vector.empty, args)
    }
  }

  def polyParam(ctx: TP.Type_paramContext): (Vector[ValDef], Vector[TypeDef]) = {
    ctx match {
      case ctx: TP.WithDependencyContext =>
        val hps = paramDefs(ctx.param_defs)
        val tps = ctx.TYPE_ID()
          .asScala
          .map(_.getText)
          .map(TypeDef.apply)
          .toVector

        (hps, tps)
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

  def constructStruct(ctx: TP.Construct_structContext): ConstructClass = {
    val tpe = typeTree(ctx.`type`)
    val pairs = Option(ctx.construct_pair)
      .map(_.asScala.map(ctx => ConstructPair(ctx.EXPR_ID.getText, expr(ctx.expr))).toVector)
      .getOrElse(Vector.empty)

    ConstructClass(tpe, pairs)
  }

  def constructModule(ctx: TP.Construct_moduleContext): ConstructModule = {
    val tpe = typeTree(ctx.`type`)

    val parents = Option(ctx.parent_pair)
      .map(_.asScala.map(ctx => ConstructPair(ctx.EXPR_ID.getText, expr(ctx.expr))))
      .getOrElse(Seq.empty)
      .to(Vector)

    val siblings = Option(ctx.sibling_pair)
      .map(_.asScala.map(ctx => ConstructPair(ctx.EXPR_ID.getText, expr(ctx.expr))))
      .getOrElse(Seq.empty)
      .to(Vector)

    ConstructModule(tpe, parents, siblings)
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
