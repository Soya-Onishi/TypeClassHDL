package tchdl

import tchdl.ast._
import tchdl.util._
import tchdl.typecheck._

class ImplMethodSigTyperTest extends TchdlFunSuite {
  def parse(filename: String): CompilationUnit =
    parseFile(_.compilation_unit)((gen, tree) => gen(tree, filename))(filename).asInstanceOf[CompilationUnit]

  def untilThisPhase(names: String*): (Seq[CompilationUnit], GlobalData) = {
    implicit val global: GlobalData = new GlobalData

    val files = names.map(buildName(rootDir, filePath, _))
    val filenames = files ++ builtInFiles
    val trees = filenames.map(parse)

    trees.foreach(Namer.exec)
    expectNoError

    trees.foreach(NamerPost.exec)
    expectNoError

    trees.foreach(BuildImplContainer.exec)
    expectNoError

    VerifyImplConflict.verifyImplConflict()
    expectNoError

    trees.foreach(TopDefTyper.exec)
    expectNoError

    trees.foreach(ImplMethodSigTyper.exec)

    val cus = trees.filter(cu => files.contains(cu.filename.get))
    (cus, global)
  }

  test("reject invalid signature impl's method") {
    val (_, global) = untilThisPhase("typerDefSig0.tchdl")
    expectError(1)(global)

    val err = global.repo.error.elems.head
    assert(err.isInstanceOf[Error.TypeMissMatch])
    val Error.TypeMissMatch(expect, actual) = err
    assert(expect == Type.intTpe(global))
    assert(actual == Type.stringTpe(global))
  }

  test("reject poly method that does not have same bounds as original") {
    val (_, global) = untilThisPhase("typerDefSig1.tchdl")
    expectError(1)(global)

    val err = global.repo.error.elems.head
    assert(err.isInstanceOf[Error.NotEnoughTPBound], showErrors(global))
  }

  test("reject poly interface implementation because of miss matching type") {
    val (_, global) = untilThisPhase("typerDefSig2.tchdl")
    expectError(2)(global)
  }

  test("raise an error because of impl's method type parameter does not match correspond tp's bounds") {
    val (_, global) = untilThisPhase("typerDefSig3.tchdl")
    expectError(1)(global)

    val err = global.repo.error.elems.head
    assert(err.isInstanceOf[Error.NotEnoughTPBound])
  }

  test("raise an error because of impl's method type parameter set bounds excessively") {
    val (_, global) = untilThisPhase("typerDefSig4.tchdl")
    expectError(1)(global)

    val err = global.repo.error.elems.head
    assert(err.isInstanceOf[Error.ExcessiveTPBound])
  }

  test("raise an error because of impl's method hardware parameter does not match correspond tp's bounds") {
    val (_, global) = untilThisPhase("typerDefSig5.tchdl")
    expectError(1)(global)

    val err = global.repo.error.elems.head
    assert(err.isInstanceOf[Error.NotEnoughHPBound])
  }

  test("raise an error because of impl's method hardware parameter set bounds excessively") {
    val (_, global) = untilThisPhase("typerDefSig6.tchdl")
    expectError(1)(global)

    val err = global.repo.error.elems.head
    assert(err.isInstanceOf[Error.ExcessiveHPBound])
  }

  test("raise an error because of impl's method parameter length mismatch expected length") {
    val (_, global) = untilThisPhase("typerDefSig7.tchdl")
    expectError(1)(global)

    val err = global.repo.error.elems.head
    assert(err.isInstanceOf[Error.ParameterLengthMismatch])
  }

  test("raise an error because of impl's method type parameter length mismatch expected length") {
    val (_, global) = untilThisPhase("typerDefSig8.tchdl")
    expectError(1)(global)

    val err = global.repo.error.elems.head
    assert(err.isInstanceOf[Error.TypeParameterLengthMismatch])
  }

  test("raise an error because of impl's method hardware parameter length mismatch expected length") {
    val (_, global) = untilThisPhase("typerDefSig9.tchdl")
    expectError(1)(global)

    val err = global.repo.error.elems.head
    assert(err.isInstanceOf[Error.HardParameterLengthMismatch])
  }

  test("raise an error because impl does not implement all methods defined at interface") {
    val (_, global) = untilThisPhase("typerDefSig10.tchdl")
    expectError(1)(global)

    val err = global.repo.error.elems.head
    assert(err.isInstanceOf[Error.RequireImplementMethod])
  }

  test("raise an error because impl try to implement method interface does not have") {
    val (_, global) = untilThisPhase("typerDefSig11.tchdl")
    expectError(1)(global)

    val err = global.repo.error.elems.head
    assert(err.isInstanceOf[Error.ImplementMethodInterfaceNotHas])
  }
}
