package tchdl

import tchdl.typecheck._
import tchdl.util._
import tchdl.ast._

class TyperTest extends TchdlFunSuite {
  def parse(filename: String): CompilationUnit =
    parseFile(_.compilation_unit)((gen, tree) => gen(tree, filename))(filename).asInstanceOf[CompilationUnit]

  def untilTyper(names: String*): (Vector[CompilationUnit], GlobalData) = {
    implicit val global: GlobalData = new GlobalData
    val specifiedFileNames = names.map(buildName(rootDir, filePath, _))
    val filenames = specifiedFileNames ++ builtInFiles
    val trees = filenames.map(parse)

    trees.foreach(Namer.exec)
    assert(global.repo.error.counts == 0, showErrors(global))

    trees.foreach(NamerPost.exec)
    assert(global.repo.error.counts == 0, showErrors(global))

    trees.foreach(BuildImplContainer.exec)
    assert(global.repo.error.counts == 0, showErrors(global))

    VerifyImplConflict.verifyImplConflict()
    assert(global.repo.error.counts == 0, showErrors(global))

    val typedTrees = trees.map(Typer.exec)
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
      .methods

    val Apply(select: Select, _, _, _) = methodF.blk.get.last
    assert(select.symbol == methodG.symbol)
  }

  test("polynomial type into mono type") {
    val (trees, global) = untilTyper("structImpl2.tchdl")
    assert(global.repo.error.counts == 0, showErrors(global))

    val select = trees.head.topDefs
      .collect { case impl: ImplementClass => impl }
      .head.methods
      .head.blk.get
      .last
      .asInstanceOf[Select]

    assert(select.tpe == Type.RefType(global.builtin.lookup("Int")))
  }

  test("call another impl's method from another impl") {
    val (trees, global) = untilTyper("structImpl3.tchdl")
    assert(global.repo.error.counts == 0, showErrors(global))

    val impls = trees.head.topDefs
      .collect { case impl: ImplementClass => impl }

    val implForSTInt = impls.filter(_.target.tp.head.expr.name == "Int").head
    val implForSTString = impls.filter(_.target.tp.head.expr.name == "String").head
    val forInt = implForSTInt.methods.filter(_.name == "forInt").head
    val forString = implForSTString.methods.filter(_.name == "forString").head
    val Apply(select: Select, _, _, _) = forInt.blk.get.last

    assert(select.symbol == forString.symbol)
  }

  test("call impl's methods but this call causes error because of type param(Int) does not meet bounds") {
    val (trees, global) = untilTyper("callMethod0.tchdl")
    assert(global.repo.error.counts == 1, showErrors(global))
  }
}
