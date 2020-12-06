package tchdl

import tchdl.ast.CompilationUnit
import tchdl.ast.TypeTree
import tchdl.{ast => frontend}
import tchdl.util._
import tchdl.backend._
import tchdl.backend.ast._
import tchdl.parser.Filename
import tchdl.typecheck._

import scala.collection.immutable.ListMap

class BackendIRGenTest extends TchdlFunSuite {
  def parse(filename: String): CompilationUnit =
    parseFile(_.compilation_unit)((gen, tree) => gen(tree, filename))(filename).asInstanceOf[CompilationUnit]

  def untilThisPhase(pkgName: Vector[String], module: String, names: String*): (Vector[ModuleContainer], Vector[MethodContainer], GlobalData) = {
    val fullnames = names.map(buildName(rootDir, filePath, _))
    val filenames = fullnames ++ builtInFiles

    val trees = filenames.map(parse)
    val moduleTree = parseString(_.`type`)((gen, tree) => gen.typeTree(tree)(Filename("")))(module).asInstanceOf[TypeTree]
    implicit val global: GlobalData = GlobalData(pkgName, moduleTree)

    trees.foreach(Namer.exec)
    expectNoError

    trees.foreach(NamerPost.exec)
    expectNoError

    trees.foreach(BuildImplContainer.exec)
    expectNoError

    VerifyImplConflict.verifyImplConflict()
    expectNoError

    val trees0 = trees.map(TopDefTyper.exec)
    expectNoError

    trees0.foreach(ImplMethodSigTyper.exec)
    expectNoError

    val trees1 = trees0.map(Typer.exec)
    expectNoError

    trees1.foreach(RefCheck.exec)
    expectNoError

    val newGlobal = global.assignCompilationUnits(trees1.toVector)
    val modules = BuildGeneratedModuleList.exec(newGlobal)
    expectNoError(newGlobal)

    val (moduleContainers, methodContainers) = BackendIRGen.exec(modules)(newGlobal)
    (moduleContainers, methodContainers, newGlobal)
  }

  test("simple module structure should be generate two module containers") {
    val (modules, methods, global) = untilThisPhase(Vector("test"), "Top", "simpleStructure.tchdl")
    val filename = buildName(rootDir, filePath, "simpleStructure.tchdl")
    val tree = global.compilationUnits.find(_.filename == filename).get

    assert(modules.length == 2)
    assert(methods.isEmpty)

    val topSymbol = tree.topDefs.find(_.symbol.name == "Top").map(_.symbol.asModuleSymbol).get
    val topTpe = BackendType(BackendTypeFlag.NoFlag, topSymbol, Vector.empty, Vector.empty)
    val top = modules.find(_.tpe == topTpe).get.bodies.head

    val subSymbol = tree.topDefs.find(_.symbol.name == "Sub").map(_.symbol.asModuleSymbol).get
    val subTpe = BackendType(BackendTypeFlag.NoFlag, subSymbol, Vector.empty, Vector.empty)

    assert(top.interfaces.isEmpty)
    assert(top.stages.isEmpty)
    assert(top.always.isEmpty)
    assert(top.fields.length == 1)

    val subDef = top.fields.head
    assert(subDef.code.isEmpty)
    assert(subDef.ret.isDefined)

    val Some(construct) = subDef.ret
    assert(construct == backend.ast.ConstructModule(Term.Variable("sub", subTpe), subTpe, Map.empty, Map.empty))
  }

  test("modules that have hardware parameters make two module containers with concrete hp values") {
    val (modules, methods, global) = untilThisPhase(Vector("test"), "Top[4]", "moduleWithHP0.tchdl")
    val filename = buildName(rootDir, filePath, "moduleWithHP0.tchdl")
    val tree = global.compilationUnits.find(_.filename == filename).get

    assert(modules.length == 2)
    assert(methods.isEmpty)

    val topSymbol = tree.topDefs.find(_.symbol.name == "Top").map(_.symbol.asModuleSymbol).get
    val topTpe = BackendType(BackendTypeFlag.NoFlag, topSymbol, Vector(HPElem.Num(4)), Vector.empty)
    val top = modules.find(_.tpe == topTpe).get.bodies.head

    val subSymbol = tree.topDefs.find(_.symbol.name == "Sub").map(_.symbol.asModuleSymbol).get
    val subTpe = BackendType(BackendTypeFlag.NoFlag, subSymbol, Vector(HPElem.Num(4)), Vector.empty)
    val sub = modules.find(_.tpe == subTpe).get.bodies.head

    val subFieldSymbol = tree.topDefs
      .collect{ case impl: frontend.ImplementClass => impl }
      .find(_.target.symbol.name == "Top")
      .get.components
      .collectFirst{ case vdef: frontend.ValDef if vdef.flag.hasFlag(Modifier.Field) => vdef }
      .get.symbol.asVariableSymbol

    assert(top.interfaces.length == 1)
    assert(top.fields.length == 1)
    assert(sub.interfaces.length == 1)

    val function = top.interfaces.head
    val add = sub.interfaces.head

    val bit = global.builtin.types.lookup("Bit")
    val bit4 = BackendType(BackendTypeFlag.NoFlag, bit, Vector(HPElem.Num(4)), Vector.empty)

    assert(function.code(0) == Temp(3, This(topTpe)))
    assert(function.code(1) == Temp(4, ReferField(Term.Temp(3, topTpe), FieldLabel(subFieldSymbol, Some(topTpe), ListMap.empty, ListMap.empty), subTpe)))
    val Temp(_, Ident(Term.Variable(functionA, _), _)) = function.code(2)
    val Temp(_, Ident(Term.Variable(functionB, _), _)) = function.code(3)
    assert(functionA.matches("function_a"))
    assert(functionB.matches("function_b"))

    assert(function.ret == CallInterface(add.label, Term.Temp(4, subTpe), Vector(Term.Temp(1, bit4), Term.Temp(2, bit4)), bit4))
  }

  test("build ALU circuit description should generate code correctly") {
    val (modules, methods, global) = untilThisPhase(Vector("test", "alu"), "Top", "ALU.tchdl")
    val aluFile = buildName(rootDir, filePath, "ALU.tchdl")
    val aluCU = global.compilationUnits.find(_.filename == aluFile).get

    assert(modules.length == 2)
    assert(methods.length == 4)

    val impls = aluCU.topDefs.collect { case impl: frontend.ImplementInterface => impl }
    val add = impls.flatMap(_.methods.find(_.name == "add")).map(_.symbol.asMethodSymbol).head
    val sub = impls.flatMap(_.methods.find(_.name == "sub")).map(_.symbol.asMethodSymbol).head

    assert(methods.exists(_.label.symbol == add))
    assert(methods.exists(_.label.symbol == sub))
  }

  test("build input interface method with internal call") {
    val (modules, methods, _) = untilThisPhase(Vector("test"), "Top", "InputCallInternal.tchdl")

    assert(modules.length == 1)
    assert(methods.isEmpty)

    val bodies = modules.head.bodies
    val inputFunc = bodies.head.interfaces.find(_.label.symbol.name == "inputFunc").get
    val internalFunc = bodies.head.interfaces.find(_.label.symbol.name == "internalFunc").get

    val topTpe = modules.head.tpe
    val bit8 = internalFunc.ret.tpe

    assert(inputFunc.code.length == 2)
    assert(inputFunc.ret == CallInterface(
      internalFunc.label,
      Term.Temp(2, topTpe),
      Vector(Term.Temp(1, bit8)),
      bit8
    ))
  }

  test("generate stage correctly") {
    val (modules, methods, _) = untilThisPhase(Vector("test"), "M", "generateStage1.tchdl")

    assert(methods.isEmpty)
    assert(modules.length == 1)

    val module = modules.head.bodies.head

    assert(module.interfaces.length == 1)
    assert(module.stages.length == 1)

    val interface = module.interfaces.head
    val stage = module.stages.head

    assert(interface.ret.isInstanceOf[Generate])
    val Generate(generatedStage, _, _, _) = interface.ret
    assert(generatedStage == stage.label)

    assert(stage.code.length == 1)
    val Abandon(Finish(finishedStage)) = stage.code.head
    assert(finishedStage == stage.label)
  }

  test("build valid stage code correctly") {
    val (modules, _, _) = untilThisPhase(Vector("test"), "M", "validSequenceCircuit.tchdl")
    val module = modules.head.bodies.head

    assert(module.stages.length == 3)

    val st1 = module.stages.find(_.label.symbol.name == "st1").get
    val st2 = module.stages.find(_.label.symbol.name == "st2").get
    val st3 = module.stages.find(_.label.symbol.name == "st3").get

    assert(st1.states.length == 2)

    val s1 = st1.states.find(_.label.symbol.name == "s1").get
    val s2 = st1.states.find(_.label.symbol.name == "s2").get

    val s1Goto = s1.code.collectFirst{ case Abandon(goto: Goto) => goto }.get
    val s1Generate = s1.code.collectFirst{ case Abandon(gen: Generate) => gen }.get

    val s2Finish = s2.code.collectFirst{ case Abandon(finish: Finish) => finish }.get
    val s2Generate = s2.code.collectFirst{ case Abandon(gen: Generate) => gen }.get

    assert(s1Goto.state.label == s2.label)
    assert(s1Generate.stage == st2.label)

    assert(s2Finish.stage == st1.label)
    assert(s2Generate.stage == st3.label)

    val st2Finish = st2.code.collectFirst{ case Abandon(finish: Finish) => finish }.get
    val st3Finish = st3.code.collectFirst{ case Abandon(finish: Finish) => finish }.get

    assert(st2Finish.stage == st2.label)
    assert(st3Finish.stage == st3.label)

    val (st1AName, _) = st1.params.head
    val (st1BName, _) = st1.params.tail.head

    assert(st1AName.matches("st1_a"), s"actual[$st1AName]")
    assert(st1BName.matches("st1_b"), s"actual[$st1BName]")
  }

  test("local variable also has hashcode") {
    val (modules, _, _) = untilThisPhase(Vector("test"), "Top", "UseLocalVariable.tchdl")

    val body = modules.head.bodies.head
    val local = body.interfaces.head.code.collectFirst{ case Variable(name, _, _) => name }.get

    assert(local.matches("func_0_local"))
  }

  test("construct enum value") {
    val (modules, _, _) = untilThisPhase(Vector("test"), "Mod", "ConstructEnum0.tchdl")
    val module = modules.head
    val interface = module.bodies.head.interfaces.head

    assert(interface.ret.isInstanceOf[ConstructEnum])
  }

  test("IR from pattern match expression generated correctly") {
    val (modules, _, _) = untilThisPhase(Vector("test"), "Top", "PatternMatch0.tchdl")

    val expr = modules.head.bodies.head.interfaces.head.ret
    assert(expr.isInstanceOf[Match])

    val Match(matched, cases, _, _) = expr

    assert(matched.isInstanceOf[Term.Temp])
    assert(cases.length == 2)

    val option = matched.asInstanceOf[Term.Temp].tpe.symbol.asEnumSymbol
    val variants = option.tpe.declares.toMap.values.toVector

    val Case(pattern0, _, _) = cases.head
    val some = pattern0.asInstanceOf[EnumPattern]
    assert(some.variant == 1)
    assert(some.patterns.length == 1)
    assert(some.patterns.head.isInstanceOf[IdentPattern])

    val Case(pattern1, _, _) = cases.tail.head
    val none = pattern1.asInstanceOf[EnumPattern]
    assert(none.variant == 0)
    assert(none.patterns.isEmpty)
  }

  test("IR from pattern match expression with condition generated correctly") {
    val (modules, _, global) = untilThisPhase(Vector("test"), "Top", "PatternMatch6.tchdl")

    assert(modules.head.bodies.length == 1)
    val body = modules.head.bodies.head
    val expr = body.interfaces.head.ret
    assert(expr.isInstanceOf[Match])

    val Match(matched, cases, _, _) = expr

    assert(matched.isInstanceOf[Term.Temp])
    assert(cases.length == 3)

    val option = matched.asInstanceOf[Term.Temp].tpe.symbol.asEnumSymbol
    val variants = option.tpe.declares.toMap.values.toVector

    val Case(pattern0, stmts0, ret0) = cases(0)
    val some0 = pattern0.asInstanceOf[EnumPattern]
    assert(some0.variant == 1)
    assert(some0.patterns.length == 1)
    assert(some0.patterns.head == LiteralPattern(BitLiteral(0, HPElem.Num(2))(global)))
    assert(stmts0.isEmpty)
    assert(ret0 == BitLiteral(2, HPElem.Num(2))(global))

    val Case(pattern1, stmts1, ret1) = cases(1)
    val some1 = pattern1.asInstanceOf[EnumPattern]
    assert(some1.variant == 1)
    assert(some1.patterns.length == 1)
    assert(some1.patterns.head.isInstanceOf[IdentPattern])
    assert(stmts1.isEmpty)
    assert(ret1.isInstanceOf[Ident])

    val Case(pattern2, stmts2, ret2) = cases(2)
    val none2 = pattern2.asInstanceOf[EnumPattern]
    assert(none2.variant == 0)
    assert(stmts2.isEmpty)
    assert(ret2 == BitLiteral(0, HPElem.Num(2))(global))
  }

  test("generate multiple impl has f and g interfaces") {
    val (modules, _, global) = untilThisPhase(Vector("test"), "Top", "multiImplForModule.tchdl")
    expectNoError(global)

    assert(modules.length == 1)
    assert(modules.head.bodies.length == 2)

    val body0 = modules.head.bodies.head
    assert(body0.interfaces.length == 1)
    val names0 = body0.interfaces.map(_.label.symbol.name)
    assert(names0.contains("f") || names0.contains("g"))

    val body1 = modules.head.bodies.head
    assert(body1.interfaces.length == 1)
    val names1 = body1.interfaces.map(_.label.symbol.name)
    assert(names1.contains("f") || names1.contains("g"))
  }

  test("generate Bit[32] from Bool") {
    val (modules, _, global) = untilThisPhase(Vector("riscv"), "ALU", "RiscvALU.tchdl")
    expectNoError(global)
  }

  test("generate simple proc") {
    val (modules, _, global) = untilThisPhase(Vector("test"), "CommenceProc", "procCommence.tchdl")
    expectNoError(global)

    val module = modules.head
    assert(module.bodies.length == 1)
    assert(module.bodies.head.interfaces.length == 1)
    assert(module.bodies.head.procs.length == 1)
    val method = module.bodies.head.interfaces.head
    val proc = module.bodies.head.procs.head
    val pblk = proc.blks.find(_.label.symbol.name == "first").get

    assert(method.ret.isInstanceOf[Commence])
    val tpe = BackendType(BackendTypeFlag.Pointer, Symbol.bit(global), Vector(HPElem.Num(2)), Vector.empty)
    assert(method.ret.tpe == tpe)
    val commence = method.ret.asInstanceOf[Commence]
    assert(commence.blkLabel == pblk.label)
    assert(commence.tpe == tpe)
  }

  test("generate simple deref") {
    val (modules, _, global) = untilThisPhase(Vector("test"), "UseDeref", "procDeref.tchdl")
    expectNoError(global)

    val module = modules.head
    val input = module.bodies.head.interfaces.head
    val derefs = input.code.collect{ case d if d.expr.isInstanceOf[Deref] => d.expr.asInstanceOf[Deref] }

    assert(derefs.length == 1)
    assert(derefs.head.tpe == BackendType.bitTpe(8)(global))
    val deref = derefs.head
    val src = input.code.collectFirst{ case Temp(id, expr) if id == deref.id.id => expr}.get

    assert(src.isInstanceOf[Ident])
    assert(src.asInstanceOf[Ident].id.name.matches("exec_0_pointer"))
  }

  test("use simple if expression") {
    val (modules, _, _) = untilThisPhase(Vector("test"), "Top", "useIfExpr.tchdl")
    val module = modules.head
    val interface = module.bodies.head.interfaces.head
    assert(interface.activeName.matches("function__active"))
    val ifExpr = interface.ret.asInstanceOf[IfExpr]
    val flag = interface.code.collectFirst{ case Temp(id, expr) if id == ifExpr.cond.id => expr }.get

    assert(flag.isInstanceOf[Ident])
    val flagIdent = flag.asInstanceOf[Ident]
    assert(flagIdent.id.name.matches("function_flag"))
  }

  test("use enum that has user defined variant ID") {
    val (modules, _, _) = untilThisPhase(Vector("test"), "ALU", "useUserDefinedVariantID.tchdl")
    val module = modules.head
    val interface = module.bodies.head.interfaces.head

    assert(interface.activeName == NameTemplate.concat("execute", NameTemplate.active))

    val m = interface.ret.asInstanceOf[Match]
    m.cases.foreach{ c => assert(c.pattern.isInstanceOf[EnumPattern])}
    val patterns = m.cases.map(c => c.pattern.asInstanceOf[EnumPattern])
    patterns.zipWithIndex.foreach{ case (p, idx) => assert(p.variant == idx) }
  }
}
