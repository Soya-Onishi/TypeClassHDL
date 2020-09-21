package tchdl

import tchdl.ast._
import tchdl.util._
import tchdl.typecheck._

class TopDefTyperTest extends TchdlFunSuite {
  def parse(filename: String): CompilationUnit =
    parseFile(_.compilation_unit)((gen, tree) => gen(tree, filename))(filename).asInstanceOf[CompilationUnit]

  def untilTopDefTyper(names: String*): (Seq[CompilationUnit], GlobalData) = {
    implicit val global: GlobalData = GlobalData()
    val files = names.map(buildName(rootDir, filePath, _))
    val filenames = files ++ builtInFiles

    val trees0 = filenames.map(parse)

    trees0.foreach(Namer.exec)
    expectNoError

    trees0.foreach(NamerPost.exec)
    expectNoError

    trees0.foreach(BuildImplContainer.exec)
    expectNoError

    VerifyImplConflict.verifyImplConflict()
    expectNoError

    val trees1 = trees0.map(TopDefTyper.exec)
    val cus = trees1.filter(cu => files.contains(cu.filename))

    (cus, global)
  }

  test("not meet bounds for type parameter in impl's interface") {
    val (_, global) = untilTopDefTyper("topdef0.tchdl")
    expectError(1)(global)

    val error = global.repo.error.elems.head
    assert(error.isInstanceOf[Error.NotMeetPartialTPBound])
  }

  test("not meet bounds for type parameter in impl's target type") {
    val (_, global) = untilTopDefTyper("topdef1.tchdl")
    expectError(1)(global)

    val error = global.repo.error.elems.head
    assert(error.isInstanceOf[Error.NotMeetPartialTPBound])
  }

  test("not meet bounds for tp vs tp in impl's target type") {
    val (_, global) = untilTopDefTyper("topdef2.tchdl")
    expectError(1)(global)

    val error = global.repo.error.elems.head
    assert(error.isInstanceOf[Error.NotMeetPartialTPBound], showErrors(global))
  }

  test("not meet bounds in where clause") {
    val (_, global) = untilTopDefTyper("topdef3.tchdl")
    expectError(1)(global)

    val error = global.repo.error.elems.head
    assert(error.isInstanceOf[Error.NotMeetPartialTPBound])
  }

  test("not meet hp bounds in where clause of struct") {
    val (_, global) = untilTopDefTyper("topdef4.tchdl")
    expectError(1)(global)
    val error = global.repo.error.elems.head
    assert(error.isInstanceOf[Error.HPBoundOutOfRange])
  }

  test("field has type that does not exists") {
    val (_, global) = untilTopDefTyper("topdef5.tchdl")
    expectError(1)(global)
    val error = global.repo.error.elems.head
    assert(error.isInstanceOf[Error.SymbolNotFound])
  }

  test("bounds of interface's method is set in this phase") {
    def verifyBounds(method: Symbol.MethodSymbol, expectHP: Vector[HPBound], expectTP: Vector[TPBound]): Unit = {
      assert(method.hpBound.length == expectHP.length)
      assert(method.tpBound.length == expectTP.length)
      (method.hpBound zip expectHP).foreach{ case (actual, expect) => assert(expect == actual) }
      (method.tpBound zip expectTP).foreach{ case (actual, expect) => assert(expect == actual) }
    }

    val (Seq(tree), global) = untilTopDefTyper("topdef6.tchdl")
    expectNoError(global)

    val interface = tree.topDefs.collectFirst{ case i: InterfaceDef => i }.get
    val f = interface.methods.find(_.name == "f").get.symbol.asMethodSymbol
    val g = interface.methods.find(_.name == "g").get.symbol.asMethodSymbol
    val h = interface.methods.find(_.name == "h").get.symbol.asMethodSymbol

    verifyBounds(
      f,
      Vector.empty,
      Vector(
        TPBound(
          Type.RefType(f.tps.head, isPointer = None),
          Vector(Type.RefType(interface.symbol.asInterfaceSymbol, isPointer = Some(false)))
        )
      )
    )

    verifyBounds(
      g,
      Vector(HPBound(
        Ident("m", Position.empty).setSymbol(g.hps.head).setTpe(Type.numTpe(global)),
        HPConstraint.Range(Vector.empty, Vector(IntLiteral(0, Position.empty)))
      )),
      Vector.empty
    )

    verifyBounds(
      h,
      Vector(HPBound(
        Ident("m", Position.empty).setSymbol(h.hps.head).setTpe(Type.numTpe(global)),
        HPConstraint.Range(Vector.empty, Vector(IntLiteral(0, Position.empty)))
      )),
      Vector(
        TPBound(
          Type.RefType(h.tps.head, isPointer = None),
          Vector(Type.RefType(interface.symbol.asInterfaceSymbol, isPointer = Some(false)))
        )
      )
    )
  }

  test("members can use parent's poly parameters") {
    val (Seq(tree), global) = untilTopDefTyper("topdef7.tchdl")
    expectNoError(global)

    val structs = tree.topDefs.collect{ case s: StructDef => s }
    val module = tree.topDefs.collect{ case m: ModuleDef => m }.head
    val interfaces = tree.topDefs.collect{ case i: InterfaceDef => i }

    val st0 = structs.find(_.name == "ST0").get
    val st1 = structs.find(_.name == "ST1").get
    val i0 = interfaces.find(_.name == "I0").get
    val i1 = interfaces.find(_.name == "I1").get

    val a = st0.fields.head.symbol
    val b = st1.fields.head.symbol
    val p = module.parents.head.symbol
    val f = i0.methods.head.symbol.tpe.asMethodType
    val g = i1.methods.head.symbol.tpe.asMethodType

    assert(a.tpe.asRefType.origin == st0.tp.head.symbol)
    assert(b.tpe.asRefType.hardwareParam.head.asInstanceOf[Ident].symbol == st1.hp.head.symbol)
    assert(p.tpe.asRefType.origin == module.tp.head.symbol)
    assert(f.params.head.origin == i0.tp.head.symbol)
    assert(f.returnType.origin == i0.tp.head.symbol)
    assert(g.params.head.hardwareParam.head.asInstanceOf[Ident].symbol == i1.hp.head.symbol)
    assert(g.returnType.hardwareParam.head.asInstanceOf[Ident].symbol == i1.hp.head.symbol)
  }

  test("type param into poly interface causes an error because of being not meet bounds") {
    val (_, global) = untilTopDefTyper("topdef8.tchdl")
    expectError(1)(global)

    val err = global.repo.error.elems.head
    assert(err.isInstanceOf[Error.NotMeetPartialTPBound])
  }

  test("hardware param into poly interface causes an error because of being not meet bounds") {
    val (_, global) = untilTopDefTyper("topdef9.tchdl")
    expectError(1)(global)

    val err = global.repo.error.elems.head
    assert(err.isInstanceOf[Error.HPBoundOutOfRange])
  }

  test("interface that has methods without modifiers causes an error") {
    val (_, global) = untilTopDefTyper("interfaceWithoutModifier0.tchdl")
    expectError(1)(global)

    val err = global.repo.error.elems.head
    assert(err.isInstanceOf[Error.InvalidModifier])
    val invalid = err.asInstanceOf[Error.InvalidModifier]
    assert(invalid.actual == Modifier.NoModifier)
  }

  test("trait that has methods with modifiers causes an error") {
    val (_, global) = untilTopDefTyper("traitWithModifier0.tchdl")
    expectError(1)(global)

    val err = global.repo.error.elems.head
    assert(err.isInstanceOf[Error.InvalidModifier])
    val invalid = err.asInstanceOf[Error.InvalidModifier]
    assert(invalid.actual == Modifier.Input)
  }

  test("interface that has a method with invalid modifier combination causes an error") {
    val (_, global) = untilTopDefTyper("interfaceWithInvalidModifier.tchdl")
    expectError(1)(global)

    val err = global.repo.error.elems.head
    assert(err.isInstanceOf[Error.InvalidModifier])
  }

  test("sub module's variable has Child modifier") {
    val (Seq(tree), global) = untilTopDefTyper("submodule0.tchdl")
    expectNoError(global)

    val impl = tree.topDefs.collectFirst{ case impl: ImplementClass => impl }.get
    val sub = impl.components.collectFirst{ case vdef: ValDef => vdef }.map(_.symbol).get

    assert(sub.name == "sub")
    assert(sub.hasFlag(Modifier.Child))
    assert(sub.hasFlag(Modifier.Field))
    assert(sub.flag == (Modifier.Child | Modifier.Field))
  }

  test("invalid type of field that has type parameter mismatch bounds") {
    val (_, global) = untilTopDefTyper("topdef10.tchdl")
    expectError(1)(global)

    val err = global.repo.error.elems.head
    assert(err.isInstanceOf[Error.NotMeetPartialTPBound])
  }

  test("passed type in enum member violates type bounds cause an error") {
    val (_, global) = untilTopDefTyper("enumDef6.tchdl")
    expectError(1)(global)

    val err = global.repo.error.elems.head
    assert(err.isInstanceOf[Error.NotMeetPartialTPBound])
  }
}
