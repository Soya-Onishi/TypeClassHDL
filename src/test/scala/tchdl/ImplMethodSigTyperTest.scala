package tchdl

import tchdl.ast._
import tchdl.util._
import tchdl.typecheck._

class ImplMethodSigTyperTest extends TchdlFunSuite {
  def parse(filename: String): CompilationUnit =
    parseFile(_.compilation_unit)((gen, tree) => gen(tree, filename))(filename).asInstanceOf[CompilationUnit]

  def untilThisPhase(names: String*): (Seq[CompilationUnit], GlobalData) = {
    implicit val global: GlobalData = GlobalData()

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

    val trees0 = trees.map(TopDefTyper.exec)
    expectNoError

    trees0.foreach(ImplMethodSigTyper.exec)

    val cus = trees0.filter(cu => files.contains(cu.filename))
    (cus, global)
  }

  test("reject invalid signature impl's method") {
    val (_, global) = untilThisPhase("typerDefSig0.tchdl")
    expectError(1)(global)

    val err = global.repo.error.elems.head
    assert(err.isInstanceOf[Error.TypeMismatch])
    val Error.TypeMismatch(expect, actual, _) = err
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
    assert(err.isInstanceOf[Error.HPBoundConstraintMismatch])
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

  test("no error to implement class") {
    val (Seq(tree), global) = untilThisPhase("structImpl0.tchdl")
    expectNoError(global)

    val st = tree.topDefs.collect{ case st @ StructDef("ST", _, _, _, _) => st }.head
    val stA = st.fields.find(_.name == "a").get
    val stB = st.fields.find(_.name == "b").get

    assert(stA.symbol.tpe =:= Type.intTpe(global))
    assert(stB.symbol.tpe =:= Type.intTpe(global))

    val impl = tree.topDefs.collect { case impl: ImplementClass => impl }.head
    val methods = impl.components.collect{ case m: MethodDef => m }
    val getA = methods.find(_.name == "getA").get
    val getB = methods.find(_.name == "getB").get

    assert(getA.symbol.tpe =:= Type.MethodType(Vector.empty, Type.intTpe(global)))
    assert(getB.symbol.tpe =:= Type.MethodType(Vector.empty, Type.intTpe(global)))
  }

  test("If signature has one erroneous type, there should be one error") {
    val (_, global) = untilThisPhase("methodDef0.tchdl")
    expectError(1)(global)

    val err = global.repo.error.elems.head
    assert(err.isInstanceOf[Error.SymbolNotFound])
  }

  test("mismatching between interface's method and impl's method causes an error") {
    val (_, global) = untilThisPhase("interfaceImplModifier.tchdl")
    expectError(1)(global)

    val err = global.repo.error.elems.head
    assert(err.isInstanceOf[Error.ModifierMismatch])
  }

  test("defining input method in struct impl causes an error") {
    val (_, global) = untilThisPhase("inputMethodStructImpl.tchdl")
    expectError(1)(global)

    val err = global.repo.error.elems.head
    assert(err.isInstanceOf[Error.InvalidModifier])

    val invalid = err.asInstanceOf[Error.InvalidModifier]
    assert(invalid.expect == Vector(Modifier.NoModifier, Modifier.Static))
    assert(invalid.actual == Modifier.Input)
  }

  test("module impl's method valid modifiers") {
    val (_, global) = untilThisPhase("allValidModifier.tchdl")
    expectNoError(global)
  }

  test("stage's parameter must be hardware type") {
    val (_, global) = untilThisPhase("stageWithSWType0.tchdl")
    expectError(1)(global)

    val err = global.repo.error.elems.head
    assert(err.isInstanceOf[Error.RequireHardwareType])
  }

  test("stage that has no parameter and return unit make no error") {
    val (_, global) = untilThisPhase("stageWithoutParam.tchdl")
    expectNoError(global)
  }

  test("stage's return type must be Unit or Future[_]") {
    val (_, global) = untilThisPhase("stageWithInvalidRet.tchdl")
    expectError(1)(global)

    val err = global.repo.error.elems.head
    assert(err.isInstanceOf[Error.RequireSpecificType])
  }

  test("internal function must cause no errors") {
    val (_, global) = untilThisPhase("InputCallInternal.tchdl")
    expectNoError(global)
  }

  test("enum that has members have no fields used as interface parameter cause no error") {
    val (_, global) = untilThisPhase("enumWithInterfaceParam0.tchdl")
    expectNoError(global)
  }

  test("enum that has a member has Int field causes no error when it is used as interface parameter") {
    val (_, global) = untilThisPhase("enumWithInterfaceParam1.tchdl")
    expectNoError(global)
  }

  test("enum Option[Int] causes no error when it is used as interface parameter type") {
    val (_, global) = untilThisPhase("enumWithInterfaceParam2.tchdl")
    expectNoError(global)
  }

  test("enum Option[Bit[8]] causes no error") {
    val (_, global) = untilThisPhase("enumWithInterfaceParam3.tchdl")
    expectNoError(global)
  }

  test("use Future[Bit[_]] as stage return type") {
    val (Seq(tree), global) = untilThisPhase("stageWithFuture.tchdl")
    expectNoError(global)

    val stage = tree.topDefs
      .collectFirst{ case impl: ImplementClass => impl }.get
      .components
      .collectFirst{ case stage: StageDef => stage }.get

    assert(stage.symbol.tpe.asMethodType.returnType == Type.futureTpe(Type.bitTpe(IntLiteral(8, Position.empty))(global))(global))
  }

  test("use This type as signature") {
    val (Seq(tree), global) = untilThisPhase("useThisTypeInTrait.tchdl")
    expectNoError(global)

    val traits = tree.topDefs.collectFirst{ case traits: InterfaceDef => traits }.get
    val impl = tree.topDefs.collectFirst{ case impl: ImplementInterface => impl }.get

    val signatureDef = traits.methods.head
    val methodDef = impl.methods.head

    val signatureTpe = signatureDef.symbol.asMethodSymbol.tpe
    val methodTpe = methodDef.symbol.asMethodSymbol.tpe

    val traitTpe = Type.RefType(traits.symbol.asInterfaceSymbol, Vector.empty, Vector.empty)
    val implTpe = impl.target.tpe.asRefType

    val expectSignatureTpe = Type.MethodType(Vector(traitTpe), traitTpe)
    val expectMethodTpe = Type.MethodType(Vector(implTpe), implTpe)

    assert(expectSignatureTpe == signatureTpe)
    assert(expectMethodTpe == methodTpe)
  }

  test("unspecified hp bound does not meet constraints for m + n + 1") {
    val (Seq(tree), global) = untilThisPhase("verifyHPBound2.tchdl")
    expectError(2)(global)

    val err0 = global.repo.error.elems(0)
    val err1 = global.repo.error.elems(1)

    assert(err0.isInstanceOf[Error.HPBoundOutOfRange])
    assert(err1.isInstanceOf[Error.HPBoundOutOfRange])
  }

  test("define field type in trait") {
    val (Seq(tree), global) = untilThisPhase("defineFieldType.tchdl")
    expectNoError(global)

    val types = tree.topDefs
      .collectFirst { case inter: InterfaceDef => inter }.get
      .types

    assert(types.length == 1)

    val symbol = types.head.symbol
    assert(symbol.name == "Output")
    assert(symbol.tpe == Type.RefType(symbol.asTypeSymbol))
  }

  test("implement field type in trait impl") {
    val (Seq(tree), global) = untilThisPhase("implFieldType.tchdl")
    expectNoError(global)

    val types = tree.topDefs
      .collectFirst { case impl: ImplementInterface => impl }.get
      .types

    assert(types.length == 1)
    assert(types.head.symbol.name == "Output")
    assert(types.head.symbol.tpe == Type.intTpe(global))
  }

  test("not implemented field type causes an error") {
    val (_, global) = untilThisPhase("implNoFieldType.tchdl")
    expectError(1)(global)

    val err = global.repo.error.elems.head
    assert(err.isInstanceOf[Error.RequireImplementType])
  }

  test("use field type as method return type") {
    val (_, global) = untilThisPhase("useFieldType.tchdl")
    expectNoError(global)
  }

  test("refer field type from method return part") {
    val (Seq(tree), global) = untilThisPhase("referFieldTypeInSignature.tchdl")
    expectNoError(global)

    val output = tree.topDefs
      .collectFirst{ case inter: InterfaceDef => inter }.get
      .types.head

    val method = tree.topDefs.collectFirst{ case method: MethodDef => method }.get

    assert(method.retTpe.symbol == output.symbol)
    assert(method.retTpe.tpe.asRefType.origin == output.symbol)
  }

  test("use Str type in where clause causes an error") {
    val (_, global) = untilThisPhase("constraintStrParam.tchdl")
    expectError(1)(global)

    val err = global.repo.error.elems.head
    assert(err.isInstanceOf[Error.RequireSpecificType])
    val e = err.asInstanceOf[Error.RequireSpecificType]

    assert(e.actual == Type.strTpe(global))
    assert(e.requires == Vector(Type.numTpe(global)))
  }
}
