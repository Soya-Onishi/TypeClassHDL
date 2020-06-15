package tchdl

import tchdl.ast._
import tchdl.util._
import tchdl.typecheck._

class TopDefTyperTest extends TchdlFunSuite {
  def parse(filename: String): CompilationUnit =
    parseFile(_.compilation_unit)((gen, tree) => gen(tree, filename))(filename).asInstanceOf[CompilationUnit]

  def untilTopDefTyper(names: String*): (Seq[CompilationUnit], GlobalData) = {
    implicit val global: GlobalData = new GlobalData
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
    val cus = trees1.filter(cu => files.contains(cu.filename.get))

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
    assert(error.isInstanceOf[Error.NotMeetHPBound])
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
      Vector(TPBound(Type.RefType(f.tps.head), Vector(Type.RefType(interface.symbol.asInterfaceSymbol))))
    )

    verifyBounds(
      g,
      Vector(HPBound(
        Ident("m").setSymbol(g.hps.head).setTpe(Type.numTpe(global)),
        HPRange.Range(
          HPRange.ExprRange(Vector.empty, Vector.empty, Vector.empty),
          HPRange.ConstantRange(IInt.PInf, IInt.Integer(0), Set.empty)
        )
      )),
      Vector.empty
    )

    verifyBounds(
      h,
      Vector(HPBound(
        Ident("m").setSymbol(h.hps.head).setTpe(Type.numTpe(global)),
        HPRange.Range(
          HPRange.ExprRange(Vector.empty, Vector.empty, Vector.empty),
          HPRange.ConstantRange(IInt.PInf, IInt.Integer(0), Set.empty)
        )
      )),
      Vector(TPBound(Type.RefType(h.tps.head), Vector(Type.RefType(interface.symbol.asInterfaceSymbol))))
    )
  }
}
