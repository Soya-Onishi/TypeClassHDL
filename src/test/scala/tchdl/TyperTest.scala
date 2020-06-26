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

    val impls = trees.head.topDefs
      .collect { case impl: ImplementClass => impl }

    val implForSTInt = impls.filter(_.target.tp.head.expr.name == "Int").head
    val implForSTString = impls.filter(_.target.tp.head.expr.name == "String").head
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

  test("constructing module with struct construct format causes an error") {
    val (_, global) = untilTyper("construct2.tchdl")
    expectError(1)(global)

    val err = global.repo.error.elems.head
    assert(err.isInstanceOf[Error.RequireParentOrSiblingIndicator])
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

  }
}
