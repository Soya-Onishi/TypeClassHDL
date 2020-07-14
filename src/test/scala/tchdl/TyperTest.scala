package tchdl

import tchdl.typecheck._
import tchdl.util._
import tchdl.ast._

class TyperTest extends TchdlFunSuite {
  def parse(filename: String): CompilationUnit =
    parseFile(_.compilation_unit)((gen, tree) => gen(tree, filename))(filename).asInstanceOf[CompilationUnit]

  def untilTyper(names: String*): (Vector[CompilationUnit], GlobalData) = {
    implicit val global: GlobalData = GlobalData()
    val specifiedFileNames = names.map(buildName(rootDir, filePath, _))
    val filenames = specifiedFileNames ++ builtInFiles
    val trees = filenames.map(parse)

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

    val typedTrees = trees0.map(Typer.exec)
    val returnedTrees = typedTrees
      .filter(tt => specifiedFileNames.contains(tt.filename.get))
      .toVector

    (returnedTrees, global)
  }

  test("lookup ST's field. This does not cause errors") {
    val (trees, global) = untilTyper("structImpl0.tchdl")
    assert(global.repo.error.counts == 0, showErrors(global))
  }

  test("lookup ST's impl method. This does not cause errors") {
    val (trees, global) = untilTyper("structImpl1.tchdl")
    assert(global.repo.error.counts == 0, showErrors(global))

    val topDefs = trees.head.topDefs
    val Vector(methodF, methodG) = topDefs
      .collect{ case impl: ImplementClass => impl }
      .head
      .components
      .collect { case m: MethodDef => m }

    val Apply(select: Select, _, _, _) = methodF.blk.get.last
    assert(select.symbol == methodG.symbol)
  }

  test("polynomial type into mono type") {
    val (trees, global) = untilTyper("structImpl2.tchdl")
    assert(global.repo.error.counts == 0, showErrors(global))

    val select = trees.head.topDefs
      .collect { case impl: ImplementClass => impl }
      .head.components
      .collect { case m: MethodDef => m }
      .head.blk.get
      .last
      .asInstanceOf[Select]

    assert(select.tpe == Type.RefType(global.builtin.types.lookup("Int")))
  }

  test("call another impl's method from another impl") {
    val (trees, global) = untilTyper("structImpl3.tchdl")
    assert(global.repo.error.counts == 0, showErrors(global))

    val impls = trees.head.topDefs.collect { case impl: ImplementClass => impl }

    val implForSTInt = impls.filter(_.target.tp.head.expr.asInstanceOf[Ident].name == "Int").head
    val implForSTString = impls.filter(_.target.tp.head.expr.asInstanceOf[Ident].name == "String").head
    val forInt = implForSTInt.components.collect { case m: MethodDef => m }.filter(_.name == "forInt").head
    val forString = implForSTString.components.collect { case m: MethodDef => m }.filter(_.name == "forString").head
    val Apply(select: Select, _, _, _) = forInt.blk.get.last

    assert(select.symbol == forString.symbol)
  }

  test("call impl's methods but this call causes error because of type param(Int) does not meet bounds") {
    val (_, global) = untilTyper("callMethod0.tchdl")
    assert(global.repo.error.counts == 1, showErrors(global))

    val err = global.repo.error.elems.head
    assert(err.isInstanceOf[Error.SymbolNotFound])
  }

  test("trying to lookup field without this accessor, this should cause an error") {
    val (_, global) = untilTyper("structImpl4.tchdl")
    assert(global.repo.error.counts == 1, showErrors(global))

    val err = global.repo.error.elems.head
    assert(err.isInstanceOf[Error.SymbolNotFound])
  }

  test("trying to call same impl's method without this accessor. this should cause an error") {
    val (Seq(tree), global) = untilTyper("structImpl5.tchdl")
    assert(global.repo.error.counts == 1, showErrors(global))

    val err = global.repo.error.elems.head
    assert(err.isInstanceOf[Error.SymbolNotFound])

    val impl = tree.topDefs.collect{ case impl: ImplementClass => impl }.head
    val methods = impl.components.collect{ case m: MethodDef => m }
    val apply = methods.find(_.name == "f").get.blk.get.last.asInstanceOf[Apply]
    assert(apply.tpe == Type.ErrorType)
  }

  test("adder module should typed in collect") {
    val (Seq(tree), global) = untilTyper("Adder.tchdl")
    expectNoError(global)
  }

  test("construct modules and attach sibling") {
    val (Seq(tree), global) = untilTyper("constructModule0.tchdl")
    expectNoError(global)
  }

  test("constructing struct with module construct format causes an error") {
    val (_, global) = untilTyper("construct1.tchdl")
    expectError(1)(global)

    val err = global.repo.error.elems.head
    assert(err.isInstanceOf[Error.RejectParentOrSiblingIndicator])
  }

  test("if expression's condition type must be Bit[1] or Bool type") {
    val (_, global) = untilTyper("ifexpr0.tchdl")
    expectNoError(global)
  }

  test("if conseq and alt expression's type must be same") {
    val (_, global) = untilTyper("ifexpr1.tchdl")
    expectError(1)(global)

    val err = global.repo.error.elems.head
    assert(err.isInstanceOf[Error.TypeMismatch])

    val mismatch = err.asInstanceOf[Error.TypeMismatch]
    assert(mismatch.expect =:= Type.stringTpe(global))
    assert(mismatch.actual =:= Type.intTpe(global))
  }

  test("condition expression must be Bit[1], Bit[m]") {
    val (_, global) = untilTyper("ifexpr2.tchdl")
    expectError(1)(global)

    val err = global.repo.error.elems.head
    assert(err.isInstanceOf[Error.RequireSpecificType])
  }

  test("method call's return type should be same as expected type of caller") {
    val (Seq(tree), global) = untilTyper("callMethod1.tchdl")
    expectNoError(global)

    val method = tree.topDefs
      .collectFirst{ case impl: ImplementClass => impl }.get
      .components
      .collectFirst{ case method: MethodDef => method }.get

    val expr = method.blk.get.last

    assert(expr.tpe =:= Type.intTpe(global))
  }

  test("val definition in blk should be no error") {
    val (Seq(tree), global) = untilTyper("valdefBlk0.tchdl")
    expectNoError(global)

    val method = tree.topDefs
      .collectFirst{ case impl: ImplementClass => impl }.get
      .components
      .collectFirst{ case method: MethodDef => method }.get

    val blk = method.blk.get
    val m = method.symbol.asMethodSymbol.hps.head

    val vdef = blk.elems.head
    val add = blk.last

    assert(vdef.isInstanceOf[ValDef])

    val vdef0 = vdef.asInstanceOf[ValDef]
    val bitSymbol = global.builtin.types.lookup("Bit")
    val expectBitTpe = Type.RefType(bitSymbol, Vector(Ident("m").setSymbol(m)), Vector.empty)

    assert(vdef0.symbol.tpe =:= expectBitTpe)
    assert(add.tpe =:= expectBitTpe)
  }

  test("implement ALU") {
    val (Seq(tree), global) = untilTyper("ALU.tchdl")
    expectNoError(global)

    val modules = tree.topDefs.collect{ case m: ModuleDef => m }
    val implClass = tree.topDefs.collect{ case impl: ImplementClass => impl }
    val implInterface = tree.topDefs.collect{ case impl: ImplementInterface => impl }
    val struct = tree.topDefs.collectFirst{ case s: StructDef => s }.get
    val topImpl = implClass.find(_.target.symbol.name == "Top").get
    val aluImpl = implClass.find(_.target.symbol.name == "ALU").get

    val complex = struct.symbol.asStructSymbol
    val complexBit8 = Type.RefType(complex, Vector.empty, Vector(Type.bitTpe(IntLiteral(8))(global)))

    val always = topImpl.components.collectFirst{ case always: AlwaysDef => always }.get
    val alwaysA = always.blk.elems.collectFirst{ case vdef @ ValDef(_, "a", _, _) => vdef }.get
    val alwaysB = always.blk.elems.collectFirst{ case vdef @ ValDef(_, "b", _, _) => vdef }.get
    val alwaysC = always.blk.elems.collectFirst{ case vdef @ ValDef(_, "c", _, _) => vdef }.get
    val alwaysD = always.blk.elems.collectFirst{ case vdef @ ValDef(_, "d", _, _) => vdef }.get

    assert(alwaysA.symbol.tpe.asRefType =:= complexBit8)
    assert(alwaysB.symbol.tpe.asRefType =:= complexBit8)
    assert(alwaysC.symbol.tpe.asRefType =:= complexBit8)
    assert(alwaysD.symbol.tpe.asRefType =:= complexBit8)
    assert(alwaysA.expr.get.tpe.asRefType =:= complexBit8)
    assert(alwaysB.expr.get.tpe.asRefType =:= complexBit8)
    assert(alwaysC.expr.get.tpe.asRefType =:= complexBit8)
    assert(alwaysD.expr.get.tpe.asRefType =:= complexBit8)

    val implAdd = implInterface.find(_.interface.symbol.name == "Add").get
    val implSub = implInterface.find(_.interface.symbol.name == "Sub").get

    val add = implAdd.methods.find(_.name == "add").get
    val addReal = add.blk.get.elems.collect{ case vdef: ValDef => vdef }.find(_.name == "real").get
    val addImag = add.blk.get.elems.collect{ case vdef: ValDef => vdef }.find(_.name == "imag").get
    val addT = Type.RefType(implAdd.tp.head.symbol.asTypeParamSymbol)
    assert(addReal.symbol.tpe.asRefType =:= addT)
    assert(addImag.symbol.tpe.asRefType =:= addT)

    val sub = implSub.methods.find(_.name == "sub").get
    val subReal = sub.blk.get.elems.collect{ case vdef: ValDef => vdef }.find(_.name == "real").get
    val subImag = sub.blk.get.elems.collect{ case vdef: ValDef => vdef }.find(_.name == "imag").get
    val subT = Type.RefType(implSub.tp.head.symbol.asTypeParamSymbol)
    assert(subReal.symbol.tpe.asRefType =:= subT)
    assert(subImag.symbol.tpe.asRefType =:= subT)

    val addThisReal = addReal.expr.collect{ case StdBinOp(_, left: Select, _) => left }.get
    val addThatReal = addReal.expr.collect{ case StdBinOp(_, _, right: Select) => right }.get
    assert(addThisReal.tpe.asRefType =:= addT)
    assert(addThatReal.tpe.asRefType =:= addT)
  }

  test("generate non existential stage causes an error") {
    val (_, global) = untilTyper("generateStage0.tchdl")
    expectError(1)(global)

    val err = global.repo.error.elems.head
    assert(err.isInstanceOf[Error.SymbolNotFound])
  }

  test("generate exist stage causes no error") {
    val (_, global) = untilTyper("generateStage1.tchdl")
    expectNoError(global)
  }

  test("use goto outside of state causes an error") {
    val (_, global) = untilTyper("gotoState0.tchdl")
    expectError(1)(global)

    val err = global.repo.error.elems.head
    assert(err.isInstanceOf[Error.GotoOutsideState.type])
  }

  test("use relay outside of stage or state causes an error") {
    val (_, global) = untilTyper("relayStage0.tchdl")
    expectError(1)(global)

    val err = global.repo.error.elems.head
    assert(err.isInstanceOf[Error.RelayOutsideStage.type])
  }

  test("valid sequence circuit") {
    val (Seq(tree), global) = untilTyper("validSequenceCircuit.tchdl")
    expectNoError(global)

    val impl = tree.topDefs.collectFirst{ case impl: ImplementClass => impl }.get
    val input = impl.components.collectFirst{ case mdef: MethodDef => mdef }.get
    val stages = impl.components.collect{ case stage: StageDef => stage }
    val st1 = stages.find(_.name == "st1").get
    val st2 = stages.find(_.name == "st2").get
    val st3 = stages.find(_.name == "st3").get

    val unitSymbol = global.builtin.types.lookup("Unit")
    val bit8 = Type.bitTpe(IntLiteral(8))(global)

    assert(input.blk.get.last.isInstanceOf[Generate])
    val inputGenerate = input.blk.get.last.asInstanceOf[Generate]
    assert(inputGenerate.symbol == st1.symbol)
    assert(inputGenerate.tpe.asRefType.origin == unitSymbol)

    val s1 = st1.states.find(_.name == "s1").get
    val s2 = st1.states.find(_.name == "s2").get

    val st1C = st1.blk.collectFirst{ case vdef: ValDef => vdef }.get
    val cRootPath = st1C.symbol.path.rootPath.filterNot(_.forall(_.isDigit))
    val cInnerPath = st1C.symbol.path.innerPath
    assert(cRootPath == Vector("st1"))
    assert(cInnerPath == Vector("c"))

    assert(s1.blk.elems.last.isInstanceOf[Goto])
    val s1Goto = s1.blk.elems.last.asInstanceOf[Goto]
    assert(s1Goto.symbol == s2.symbol)

    assert(s1.blk.last.isInstanceOf[Generate])
    val s1Generate = s1.blk.last.asInstanceOf[Generate]
    assert(s1Generate.symbol == st2.symbol)
    assert(s1Generate.tpe.asRefType.origin == unitSymbol)
    assert(s1Generate.params.head.tpe =:= bit8)

    assert(s2.blk.last.isInstanceOf[Relay])
    val s2Generate = s2.blk.last.asInstanceOf[Relay]
    assert(s2Generate.symbol == st3.symbol)
    assert(s2Generate.tpe.asRefType.origin == unitSymbol)
    assert(s2Generate.params.head.tpe =:= bit8)
  }

  test("modules that call sibling module interfaces cause no errors") {
    val (_, global) = untilTyper("useSiblingInterface.tchdl")
    expectNoError(global)
  }

  test("input interface with Bit[8] return type calls sub module's input interface has unit return type causes an type mismatch error") {
    val (_, global) = untilTyper("inputInterfaceCallUnitInterface.tchdl")
    expectError(1)(global)

    val error = global.repo.error.elems.head
    assert(error.isInstanceOf[Error.TypeMismatch])
    val Error.TypeMismatch(expect, actual) = error
    assert(expect =:= Type.unitTpe(global))
    assert(actual =:= Type.bitTpe(IntLiteral(8))(global))
  }

  test("construct enum") {
    val (Seq(tree), global) = untilTyper("ConstructEnum0.tchdl")
    expectNoError(global)

    val impl = tree.topDefs.collectFirst{ case impl: ImplementClass => impl }.get
    val method = impl.components.collectFirst{ case m: MethodDef => m }.get
    val construct = method.blk.get.last.asInstanceOf[ConstructEnum]
    val opt = tree.topDefs.collectFirst{ case enum: EnumDef => enum }.get
    val some = opt.members.find(_.name == "Some").get

    assert(construct.symbol == some.symbol)
    assert(construct.tpe.asRefType.origin == opt.symbol)
    assert(construct.target.expr.tpe.asRefType.origin == opt.symbol)
    assert(construct.tpe.asRefType.hardwareParam.isEmpty)
    assert(construct.tpe.asRefType.typeParam == Vector(Type.bitTpe(IntLiteral(2))(global)))
  }

  test("simple pattern match") {
    val (Seq(tree), global) = untilTyper("PatternMatch0.tchdl")
    expectNoError(global)

    val matchExpr = tree.topDefs
      .collectFirst{ case impl: ImplementClass => impl }.get
      .components
      .collectFirst{ case method: MethodDef => method}.get
      .blk.get
      .last

    assert(matchExpr.tpe == Type.bitTpe(IntLiteral(2))(global))
    val Match(_, Vector(some, _)) = matchExpr
    assert(some.exprs.last == Ident("bit"))
    assert(some.exprs.last.asInstanceOf[Ident].tpe == Type.bitTpe(IntLiteral(2))(global))

    val bitSymbol = some.pattern.exprs.head.asInstanceOf[Ident].symbol
    assert(some.exprs.last.asInstanceOf[Ident].symbol == bitSymbol)
  }

  test("simple pattern match not exhaustive") {
    val (_, global) = untilTyper("PatternMatch1.tchdl")
    expectError(1)(global)

    val err = global.repo.error.elems.head
    assert(err.isInstanceOf[Error.NotExhaustiveEnum])
  }

  test("pattern match but enum type mismatch") {
    val (_, global) = untilTyper("PatternMatch2.tchdl")
    expectError(2)(global)

    val errs = global.repo.error.elems
    assert(errs(0).isInstanceOf[Error.TypeMismatch])
    assert(errs(1).isInstanceOf[Error.TypeMismatch])
  }

  test("pattern match literal type mismatch") {
    val (_, global) = untilTyper("PatternMatch3.tchdl")
    expectError(1)(global)

    val err = global.repo.error.elems.head
    assert(err.isInstanceOf[Error.TypeMismatch])
  }

  test("each case of type in pattern match does not meet") {
    val (_, global) = untilTyper("PatternMatch4.tchdl")
    expectError(1)(global)

    val err = global.repo.error.elems.head
    assert(err.isInstanceOf[Error.TypeMismatch])
  }

  test("not exhaustive error occurred because of Some does not have identity pattern") {
    val (_, global) = untilTyper("PatternMatch5.tchdl")
    expectError(1)(global)

    val err = global.repo.error.elems.head
    assert(err.isInstanceOf[Error.NotExhaustiveEnum])
  }

  test("pattern match of software type with bit literal causes an error") {
    val (_, global) = untilTyper("PatternMatch8.tchdl")
    expectError(1)(global)

    val err = global.repo.error.elems.head
    assert(err.isInstanceOf[Error.CannotUseBitLitForSWPattern])
  }

  test("return Future value in stage does not cause any errors") {
    val (_, global) = untilTyper("stageWithFuture.tchdl")
    expectNoError(global)
  }

  test("static method definition does not cause any error") {
    val (_, global) = untilTyper("defineStaticMethod.tchdl")
    expectNoError(global)
  }

  test("static method call with appropriate form does not cause an error") {
    val (Seq(tree), global) = untilTyper("callStaticMethod.tchdl")
    expectNoError(global)

    val st = TypeTree(Ident("ST"), Vector.empty, Vector.empty)
    val mod = TypeTree(Ident("Mod"), Vector.empty, Vector.empty)

    val stImpl = tree.topDefs.collectFirst{ case impl: ImplementClass if impl.target == st => impl }.get
    val modImpl = tree.topDefs.collectFirst{ case impl: ImplementClass if impl.target == mod => impl }.get

    val methodSymbol = stImpl.components.head.symbol.asMethodSymbol
    val apply @ Apply(select: StaticSelect, _, _, _) = modImpl.components.head.asInstanceOf[MethodDef].blk.get.last

    assert(select.symbol == methodSymbol)
    assert(apply.tpe == methodSymbol.tpe.asMethodType.returnType)
  }

  test("use `this` in static method causes an error") {
    val (_, global) = untilTyper("useThisInStatic.tchdl")
    expectError(1)(global)

    val err = global.repo.error.elems.head
    assert(err == Error.UsingSelfInsideStatic)
  }

  test("use This as accessor of static method") {
    val (Seq(tree), global) = untilTyper("useThisToCallStatic.tchdl")
    expectNoError(global)

    val impl = tree.topDefs.collectFirst { case impl: ImplementClass => impl }.get
    val called = impl.components.collectFirst { case method: MethodDef if method.name == "called" => method }.get
    val caller = impl.components.collectFirst { case method: MethodDef if method.name == "caller" => method }.get
    val Apply(select: StaticSelect, _, _, _) = caller.blk.get.last

    assert(select.symbol == called.symbol)
  }

  test("top level method definition") {
    val (Seq(tree), global) = untilTyper("topLevelMethod.tchdl")
    expectNoError(global)

    val method = tree.topDefs.collectFirst{ case m: MethodDef => m }.get
    val intTpe = Type.intTpe(global)
    val expectTpe = Type.MethodType(Vector(intTpe, intTpe), intTpe)
    assert(method.symbol.isMethodSymbol)
    assert(method.symbol.tpe == expectTpe)
  }

  test("call top level method") {
    val (Seq(tree), global) = untilTyper("callTopLevelMethod.tchdl")
    expectNoError(global)

    val method = tree.topDefs.collectFirst{ case m: MethodDef => m }.get
    val implMethod = tree.topDefs
      .collectFirst{ case impl: ImplementClass => impl }.get
      .components
      .collectFirst{ case m: MethodDef => m }.get

    val Apply(name: Ident, _, _, _) = implMethod.blk.get.last
    val methodSymbol = name.symbol

    assert(methodSymbol == method.symbol)
  }
}
