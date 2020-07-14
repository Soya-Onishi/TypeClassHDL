package tchdl

import tchdl.ast._
import tchdl.util._

class ParseTest extends TchdlFunSuite {
  test("binary operation test") {
    def binop(left: Expression, right: Expression, op: String): StdBinOp = {
      val operator = op match {
        case "+" => Operation.Add
        case "-" => Operation.Sub
        case "*" => Operation.Mul
        case "/" => Operation.Div
      }

      StdBinOp(operator, left, right)
    }

    val parser = parseString(_.expr)((gen, tree) => gen.expr(tree))_
    assert(parser("1 + 10") == binop(IntLiteral(1), IntLiteral(10), "+"))
    assert(parser("10 - d") == binop(IntLiteral(10), Ident("d"), "-"))
    assert(parser("a * 10") == binop(Ident("a"), IntLiteral(10), "*"))
    assert(parser("b / c") == binop(Ident("b"), Ident("c"), "/"))
  }

  test("apply parse test") {
    def apply(name: String)(hps: HPExpr*)(tps: TypeTree*)(args: Expression*) =
      Apply(Ident(name), hps.toVector, tps.toVector, args.toVector)

    def typeTree(name: String) = TypeTree(Ident(name), Vector.empty, Vector.empty)

    val parser = parseString(_.expr)((gen, tree) => gen.expr(tree))_

    assert(parser("a(b, 10)") == apply("a")()()(Ident("b"), IntLiteral(10)))
    assert(parser("a[Int, String](b)") == apply("a")()(typeTree("Int"), typeTree("String"))(Ident("b")))
    assert(parser("a[1](b)") == apply("a")(IntLiteral(1))()(Ident("b")))
    assert(parser("a[b, Int]()") == apply("a")(Ident("b"))(typeTree("Int"))())
  }

  test("struct definitions test") {
    def field(name: String, tpe: TypeTree): ValDef =
      ValDef(Modifier.Field, name, Some(tpe), None)

    val parser = parseString(_.top_definition)((gen, tree) => gen.topDefinition(tree)) _

    assert(
      parser("struct A { a: Int, b: Bit[3] }") ==
      StructDef(
        "A",
        Vector.empty,
        Vector.empty,
        Vector.empty,
        Vector(
          field("a", TypeTree(Ident("Int"), Vector.empty, Vector.empty)),
          field("b", TypeTree(Ident("Bit"), Vector(IntLiteral(3)), Vector.empty))
        )
      )
    )
  }

  test("module definition test") {
    val parser = parseString(_.top_definition)((gen, tree) => gen.topDefinition(tree)) _

    assert(
      parser("module Mod {}") ==
        ModuleDef(
          "Mod",
          Vector.empty,
          Vector.empty,
          Vector.empty,
          Vector.empty,
          Vector.empty,
        )
    )

    assert(
      parser("module Mod { parent: p: M1 sibling: s: M2 }") ==
      ModuleDef (
        "Mod",
        Vector.empty,
        Vector.empty,
        Vector.empty,
        Vector(ValDef(Modifier.Parent | Modifier.Field, "p", Some(TypeTree(Ident("M1"), Vector.empty, Vector.empty)), None)),
        Vector(ValDef(Modifier.Sibling | Modifier.Field, "s", Some(TypeTree(Ident("M2"), Vector.empty, Vector.empty)), None)),
      )
    )

    assert(
      parser("module Mod[m: Num, T] where m: min 1 & max 3, T: I0 + I1") ==
      ModuleDef (
        "Mod",
        Vector(ValDef(Modifier.Local, "m", Some(TypeTree(Ident("Num"), Vector.empty, Vector.empty)), None)),
        Vector(TypeDef("T")),
        Vector(
          HPBoundTree(
            Ident("m"),
            Vector(
              RangeExpr.Min(IntLiteral(1)),
              RangeExpr.Max(IntLiteral(3))
            )
          ),
          TPBoundTree(
            TypeTree(Ident("T"), Vector.empty, Vector.empty),
            Vector(
              TypeTree(Ident("I0"), Vector.empty, Vector.empty),
              TypeTree(Ident("I1"), Vector.empty, Vector.empty)
            )
          )
        ),
        Vector.empty,
        Vector.empty,
      )
    )
  }

  test("impl class test") {
    val parser = parseString(_.top_definition)((gen, tree) => gen.topDefinition(tree)) _

    assert(
      parser("impl[T] C[T] { def f() -> Unit {} }") ==
      ImplementClass(
        TypeTree(Ident("C"), Vector.empty, Vector(TypeTree(Ident("T"), Vector.empty, Vector.empty))),
        Vector.empty,
        Vector(TypeDef("T")),
        Vector.empty,
        Vector(MethodDef(
          Modifier.NoModifier,
          "f",
          Vector.empty,
          Vector.empty,
          Vector.empty,
          Vector.empty,
          TypeTree(Ident("Unit"), Vector.empty, Vector.empty),
          Some(Block(Vector.empty, UnitLiteral()))
        ))
      )
    )
  }

  test("impl interface test") {
    val parser = parseString(_.top_definition)((gen, tree) => gen.topDefinition(tree)) _

    assert(
      parser("impl[m: Num, T] I[m] for Type[T] { }") ==
      ImplementInterface(
        TypeTree(Ident("I"), Vector(Ident("m")), Vector.empty),
        TypeTree(Ident("Type"), Vector.empty, Vector(TypeTree(Ident("T"), Vector.empty, Vector.empty))),
        Vector(ValDef(Modifier.Local, "m", Some(TypeTree(Ident("Num"), Vector.empty, Vector.empty)), None)),
        Vector(TypeDef("T")),
        Vector.empty,
        Vector.empty
      )
    )
  }

  test("parse builtin types") {
    val filename = buildName(rootDir, builtinPath, "types.tchdl")

    parseFile(_.compilation_unit)((gen, tree) => gen(tree, filename))(filename)
  }

  test("implement module with some type components") {
    val filename = buildName(rootDir, filePath, "moduleImpl0.tchdl")
    val tree = parseFile(_.compilation_unit)((gen, tree) => gen(tree, filename))(filename).asInstanceOf[CompilationUnit]

    val impl = tree.topDefs.collect{ case impl: ImplementClass => impl }.head
    val vdefs = impl.components.collect{ case vdef: ValDef => vdef }

    val in = vdefs.find(_.name == "in").get
    val inter = vdefs.find(_.name == "inter").get
    val out = vdefs.find(_.name == "out").get

    val register = vdefs.find(_.name == "register").get
    val sub = vdefs.find(_.name == "sub").get

    val method = impl.components.collect{ case method: MethodDef => method }
    val stage = impl.components.collect{ case stage: StageDef => stage }
    val always = impl.components.collect{ case always: AlwaysDef => always }

    assert(in.flag == (Modifier.Input | Modifier.Field))
    assert(inter.flag == (Modifier.Internal | Modifier.Field))
    assert(out.flag == (Modifier.Output | Modifier.Field))

    assert(register.flag == (Modifier.Register | Modifier.Field))

    assert(sub.expr.isDefined)
    assert(sub.expr.get.isInstanceOf[ConstructModule])

    assert(method.length == 1)
    assert(stage.length == 1)
    assert(always.length == 1)
  }

  test ("parse sibling and input method") {
    val tree = parseString(_.method_def)((gen, tree) => gen.methodDef(tree)) {
      "sibling input def f(a: Bit[4]) -> Bit[4] { a }"
    }

    val MethodDef(flag, _, _, _, _, _, _, _) = tree.asInstanceOf[MethodDef]
    assert(flag.hasFlag(Modifier.Sibling))
    assert(flag.hasFlag(Modifier.Input))
  }

  test("construct two modules") {
    val filename = buildName(rootDir, filePath, "constructModule0.tchdl")
    val tree = parseFile(_.compilation_unit)((gen, tree) => gen(tree, filename))(filename).asInstanceOf[CompilationUnit]

    val impl = tree.topDefs.collect { case impl: ImplementClass => impl }.head
    val vdefs = impl.components.map{ case vdef: ValDef => vdef }
    val s0 = vdefs.find(_.name == "s0").get
    val s1 = vdefs.find(_.name == "s1").get

    assert(s0.expr.get.isInstanceOf[ConstructModule])
    assert(s1.expr.get.isInstanceOf[ConstructModule])
  }

  test("constructing module with struct construct format causes an error") {
    val filename = buildName(rootDir, filePath, "construct2.tchdl")

    assertThrows[AssertionError](parseFile(_.compilation_unit)((gen, tree) => gen(tree, filename))(filename).asInstanceOf[CompilationUnit])
  }

  test("enum Option definition parsed correctly") {
    val filename = buildName(rootDir, filePath, "enumOption.tchdl")
    val tree = parseFile(_.compilation_unit)((gen, tree) => gen(tree, filename))(filename).asInstanceOf[CompilationUnit]

    val topDefs = tree.topDefs
    val enums = topDefs.collect{ case enum: EnumDef => enum }
    assert(enums.length == 1)
    val option = enums.head
    assert(option.name == "Option")
    assert(option.hp.isEmpty)
    assert(option.tp.length == 1)
    assert(option.tp.head.name == "T")

    val fields = option.members
    assert(fields.length == 2)

    val none = fields.head
    assert(none.name == "None")
    assert(none.fields.isEmpty)

    val some = fields.tail.head
    assert(some.name == "Some")
    assert(some.fields.length == 1)
    assert(some.fields.head.expr == Ident("T"))
  }

  test("access Type from another package") {
    val filename = buildName(rootDir, filePath, "UseAnotherPackageType.tchdl")
    val tree = parseFile(_.compilation_unit)((gen, tree) => gen(tree, filename))(filename).asInstanceOf[CompilationUnit]

    val topDefs = tree.topDefs
    val structA = topDefs
      .collectFirst{ case structDef: StructDef => structDef }.get
      .fields
      .find(_.name == "a").get

    assert(structA.tpeTree.get == TypeTree(SelectPackage(Vector("test1"), "ST1"), Vector.empty, Vector.empty))

    val method = topDefs
      .collectFirst{ case impl: ImplementClass if impl.target.expr.isInstanceOf[Ident] => impl }.get
      .components
      .collectFirst{ case method: MethodDef => method }.get

    assert(method.retTpe == TypeTree(SelectPackage(Vector("test1"), "ST1"), Vector.empty, Vector.empty))

    val construct = method.blk.get.last.asInstanceOf[ConstructClass]
    assert(construct.target == TypeTree(SelectPackage(Vector("test1"), "ST1"), Vector.empty, Vector.empty))
  }

  test("construct enum") {
    val filename = buildName(rootDir, filePath, "ConstructEnum0.tchdl")
    val tree = parseFile(_.compilation_unit)((gen, tree) => gen(tree, filename))(filename).asInstanceOf[CompilationUnit]

    val expr = tree.topDefs
      .collectFirst{ case impl: ImplementClass => impl }.get
      .components
      .collectFirst{ case method: MethodDef => method }.get
      .blk.get
      .last

    assert(expr.isInstanceOf[ConstructEnum])
    val construct = expr.asInstanceOf[ConstructEnum]

    assert(construct.target.expr.isInstanceOf[StaticSelect])
    val select = construct.target.expr.asInstanceOf[StaticSelect]

    assert(select.prefix == TypeTree(Ident("Opt"), Vector.empty, Vector(TypeTree(Ident("Bit"), Vector(IntLiteral(2)), Vector.empty))))
    assert(select.name == "Some")
    assert(construct.target.hp.isEmpty)
    assert(construct.target.tp.isEmpty)
  }

  test("pattern matching test") {
    val Match(expr, cases) = parseString(_.expr)((gen, tree) => gen.expr(tree))(
      """
        |match expr {
        |  case Pattern:::A(a, b) =>
        |  case Pattern:::B(0, 0b00) =>
        |  case Pattern:::C("abc", ()) =>
        |}
        |""".stripMargin
    )

    def pattern(name: String, expr: PatternExpr*): EnumPattern = {
      val typeTree = TypeTree(
        StaticSelect(TypeTree(Ident("Pattern"), Vector.empty, Vector.empty), name),
        Vector.empty,
        Vector.empty
      )

      EnumPattern(typeTree, expr.toVector)
    }

    assert(expr == Ident("expr"))
    assert(cases(0).pattern == pattern("A", Ident("a"), Ident("b")))
    assert(cases(1).pattern == pattern("B", IntLiteral(0), BitLiteral(0, 2)))
    assert(cases(2).pattern == pattern("C", StringLiteral("abc"), UnitLiteral()))
  }

  test("parse static method definition") {
    val filename = buildName(rootDir, filePath, "defineStaticMethod.tchdl")
    val tree = parseFile(_.compilation_unit)((gen, tree) => gen(tree, filename))(filename).asInstanceOf[CompilationUnit]

    val traits = tree.topDefs.collectFirst{ case traits: InterfaceDef if traits.flag.hasFlag(Modifier.Trait) => traits }.get
    val interface = tree.topDefs.collectFirst{ case traits: InterfaceDef if traits.flag.hasFlag(Modifier.Interface) => traits }.get

    val st = TypeTree(Ident("ST"), Vector.empty, Vector.empty)
    val mod = TypeTree(Ident("Mod"), Vector.empty, Vector.empty)

    val traitImpl = tree.topDefs.collectFirst{ case impl: ImplementInterface if impl.target == st => impl }.get
    val interfaceImpl = tree.topDefs.collectFirst { case impl: ImplementInterface if impl.target == mod => impl }.get

    val stImpl = tree.topDefs.collectFirst { case impl: ImplementClass if impl.target == st => impl }.get
    val modImpl = tree.topDefs.collectFirst { case impl: ImplementClass if impl.target == mod => impl }.get

    assert(traits.methods.head.flag == Modifier.Static)
    assert(interface.methods.head.flag == Modifier.Static)
    assert(traitImpl.methods.head.flag == Modifier.Static)
    assert(interfaceImpl.methods.head.flag == Modifier.Static)
    assert(stImpl.components.head.asInstanceOf[MethodDef].flag == Modifier.Static)
    assert(modImpl.components.head.asInstanceOf[MethodDef].flag == Modifier.Static)
  }

  test("parse static method call") {
    val Apply(prefix, hargs, targs, args) = parseString(_.expr)((gen, tree) => gen.expr(tree)) {
      """Int:::from("1")"""
    }

    val int = TypeTree(Ident("Int"), Vector.empty, Vector.empty)

    assert(hargs == Vector.empty)
    assert(targs == Vector.empty)
    assert(args == Vector(StringLiteral("1")))
    assert(prefix == StaticSelect(int, "from"))
  }

  test("parse top level method definition") {
    val filename = buildName(rootDir, filePath, "topLevelMethod.tchdl")
    val tree = parseFile(_.compilation_unit)((gen, tree) => gen(tree, filename))(filename).asInstanceOf[CompilationUnit]
  }
}
