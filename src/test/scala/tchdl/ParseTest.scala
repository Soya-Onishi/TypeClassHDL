package tchdl

import tchdl.ast._
import tchdl.parser.Filename
import tchdl.util._

class ParseTest extends TchdlFunSuite {
  def pos = Position.empty
  def file = Filename("")

  test("binary operation test") {
    def binop(left: Expression, right: Expression, op: String): StdBinOp = {
      val operator = op match {
        case "+" => Operation.Add
        case "-" => Operation.Sub
        case "*" => Operation.Mul
        case "/" => Operation.Div
      }

      StdBinOp(operator, left, right, pos)
    }

    val parser = parseString(_.expr)((gen, tree) => gen.expr(tree)(file))_
    assert(parser("1 + 10") == binop(IntLiteral(1, pos), IntLiteral(10, pos), "+"))
    assert(parser("10 - d") == binop(IntLiteral(10, pos), Ident("d", pos), "-"))
    assert(parser("a * 10") == binop(Ident("a", pos), IntLiteral(10, pos), "*"))
    assert(parser("b / c") == binop(Ident("b", pos), Ident("c", pos), "/"))
  }

  test("apply parse test") {
    def apply(name: String)(hps: HPExpr*)(tps: TypeTree*)(args: Expression*) =
      Apply(Ident(name, pos), hps.toVector, tps.toVector, args.toVector, pos)

    def typeTree(name: String) = TypeTree(Ident(name, pos), Vector.empty, Vector.empty, isPointer = false, pos)

    val parser = parseString(_.expr)((gen, tree) => gen.expr(tree)(file))_

    assert(parser("a(b, 10)") == apply("a")()()(Ident("b", pos), IntLiteral(10, pos)))
    assert(parser("a[Int, String](b)") == apply("a")()(typeTree("Int"), typeTree("String"))(Ident("b", pos)))
    assert(parser("a[1](b)") == apply("a")(IntLiteral(1, pos))()(Ident("b", pos)))
    assert(parser("a[b, Int]()") == apply("a")(Ident("b", pos))(typeTree("Int"))())
  }

  test("struct definitions test") {
    def field(name: String, tpe: TypeTree): ValDef =
      ValDef(Modifier.Field, name, Some(tpe), None, pos)

    val parser = parseString(_.top_definition)((gen, tree) => gen.topDefinition(tree)(file)) _

    assert(
      parser("struct A { a: Int, b: Bit[3] }") ==
      StructDef(
        "A",
        Vector.empty,
        Vector.empty,
        Vector.empty,
        Vector(
          field("a", TypeTree(Ident("Int", pos), Vector.empty, Vector.empty, isPointer = false, pos)),
          field("b", TypeTree(Ident("Bit", pos), Vector(IntLiteral(3, pos)), Vector.empty, isPointer = false, pos))
        ),
        pos
      )
    )
  }

  test("module definition test") {
    val parser = parseString(_.top_definition)((gen, tree) => gen.topDefinition(tree)(file)) _

    assert(
      parser("module Mod {}") ==
        ModuleDef(
          "Mod",
          Vector.empty,
          Vector.empty,
          Vector.empty,
          Vector.empty,
          Vector.empty,
          pos
        )
    )

    assert(
      parser("module Mod { parent: p: M1 sibling: s: M2 }") ==
      ModuleDef (
        "Mod",
        Vector.empty,
        Vector.empty,
        Vector.empty,
        Vector(ValDef(Modifier.Parent | Modifier.Field, "p", Some(TypeTree(Ident("M1", pos), Vector.empty, Vector.empty, isPointer = false, pos)), None, pos)),
        Vector(ValDef(Modifier.Sibling | Modifier.Field, "s", Some(TypeTree(Ident("M2", pos), Vector.empty, Vector.empty, isPointer = false, pos)), None, pos)),
        pos
      )
    )

    assert(
      parser("module Mod[m: Num, T] where m: min 1 & max 3, T: I0 + I1") ==
      ModuleDef (
        "Mod",
        Vector(ValDef(Modifier.Local, "m", Some(TypeTree(Ident("Num", pos), Vector.empty, Vector.empty, isPointer = false, pos)), None, pos)),
        Vector(TypeDef(Modifier.Param, "T", None, pos)),
        Vector(
          HPBoundTree(
            Ident("m", pos),
            Vector(
              RangeExpr.Min(IntLiteral(1, pos)),
              RangeExpr.Max(IntLiteral(3, pos))
            ),
            pos
          ),
          TPBoundTree(
            TypeTree(Ident("T", pos), Vector.empty, Vector.empty, isPointer = false, pos),
            Vector(
              TypeTree(Ident("I0", pos), Vector.empty, Vector.empty, isPointer = false, pos),
              TypeTree(Ident("I1", pos), Vector.empty, Vector.empty, isPointer = false, pos)
            ),
            pos
          )
        ),
        Vector.empty,
        Vector.empty,
        pos
      )
    )
  }

  test("impl class test") {
    val parser = parseString(_.top_definition)((gen, tree) => gen.topDefinition(tree)(file)) _

    assert(
      parser("impl[T] C[T] { def f() -> Unit {} }") ==
      ImplementClass(
        TypeTree(Ident("C", pos), Vector.empty, Vector(TypeTree(Ident("T", pos), Vector.empty, Vector.empty, isPointer = false, pos)), isPointer = false, pos),
        Vector.empty,
        Vector(TypeDef(Modifier.Param, "T", None, pos)),
        Vector.empty,
        Vector(MethodDef(
          Vector.empty,
          Modifier.NoModifier,
          "f",
          Vector.empty,
          Vector.empty,
          Vector.empty,
          Vector.empty,
          TypeTree(Ident("Unit", pos), Vector.empty, Vector.empty, isPointer = false, pos),
          Some(Block(Vector.empty, UnitLiteral(pos), pos)),
          pos
        )),
        pos
      )
    )
  }

  test("impl interface test") {
    val parser = parseString(_.top_definition)((gen, tree) => gen.topDefinition(tree)(file)) _

    assert(
      parser("impl[m: Num, T] I[m] for Type[T] { }") ==
      ImplementInterface(
        TypeTree(Ident("I", pos), Vector(Ident("m", pos)), Vector.empty, isPointer = false, pos),
        TypeTree(Ident("Type", pos), Vector.empty, Vector(TypeTree(Ident("T", pos), Vector.empty, Vector.empty, isPointer = false, pos)), isPointer = false, pos),
        Vector(ValDef(Modifier.Local, "m", Some(TypeTree(Ident("Num", pos), Vector.empty, Vector.empty, isPointer = false, pos)), None, pos)),
        Vector(TypeDef(Modifier.Param, "T", None, pos)),
        Vector.empty,
        Vector.empty,
        Vector.empty,
        pos
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
    val tree = parseString(_.method_def)((gen, tree) => gen.methodDef(tree)(file)) {
      "sibling input def f(a: Bit[4]) -> Bit[4] { a }"
    }

    val MethodDef(_, flag, _, _, _, _, _, _, _) = tree.asInstanceOf[MethodDef]
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
    assert(some.fields.head.expr == Ident("T", pos))
  }

  test("access Type from another package") {
    val filename = buildName(rootDir, filePath, "UseAnotherPackageType.tchdl")
    val tree = parseFile(_.compilation_unit)((gen, tree) => gen(tree, filename))(filename).asInstanceOf[CompilationUnit]

    val topDefs = tree.topDefs
    val structA = topDefs
      .collectFirst{ case structDef: StructDef => structDef }.get
      .fields
      .find(_.name == "a").get

    assert(structA.tpeTree.get == TypeTree(SelectPackage(Vector("test1"), "ST1", pos), Vector.empty, Vector.empty, isPointer = false, pos))

    val method = topDefs
      .collectFirst{ case impl: ImplementClass if impl.target.expr.isInstanceOf[Ident] => impl }.get
      .components
      .collectFirst{ case method: MethodDef => method }.get

    assert(method.retTpe == TypeTree(SelectPackage(Vector("test1"), "ST1", pos), Vector.empty, Vector.empty, isPointer = false, pos))

    val construct = method.blk.get.last.asInstanceOf[ConstructClass]
    assert(construct.target == TypeTree(SelectPackage(Vector("test1"), "ST1", pos), Vector.empty, Vector.empty, isPointer = false, pos))
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

    assert(select.prefix == TypeTree(Ident("Opt", pos), Vector.empty, Vector(TypeTree(Ident("Bit", pos), Vector(IntLiteral(2, pos)), Vector.empty, isPointer = false, pos)), isPointer = false, pos))
    assert(select.name == "Some")
    assert(construct.target.hp.isEmpty)
    assert(construct.target.tp.isEmpty)
  }

  test("pattern matching test") {
    val Match(expr, cases) = parseString(_.expr)((gen, tree) => gen.expr(tree)(file))(
      """
        |match expr {
        |  case Pattern:::A(a, b) =>
        |  case Pattern:::B(0, 0b00) =>
        |  case Pattern:::C(()) =>
        |}
        |""".stripMargin
    )

    def pattern(name: String, expr: MatchPattern*): EnumPattern = {
      val typeTree = TypeTree(
        StaticSelect(TypeTree(Ident("Pattern", pos), Vector.empty, Vector.empty, isPointer = false, pos), name, pos),
        Vector.empty,
        Vector.empty,
        isPointer = false,
        pos
      )

      EnumPattern(typeTree, expr.toVector, pos)
    }

    def ident(name: String) = IdentPattern(Ident(name, pos), pos)
    def int(value: Int) = LiteralPattern(IntLiteral(value, pos), pos)
    def bit(value: Int, width: Int) = LiteralPattern(BitLiteral(value, width, pos), pos)
    def unit() = LiteralPattern(UnitLiteral(pos), pos)

    assert(expr == Ident("expr", pos))
    assert(cases(0).pattern == pattern("A", ident("a"), ident("b")))
    assert(cases(1).pattern == pattern("B", int(0), bit(0, 2)))
    assert(cases(2).pattern == pattern("C", unit()))
  }

  test("parse static method definition") {
    val filename = buildName(rootDir, filePath, "defineStaticMethod.tchdl")
    val tree = parseFile(_.compilation_unit)((gen, tree) => gen(tree, filename))(filename).asInstanceOf[CompilationUnit]

    val traits = tree.topDefs.collectFirst{ case traits: InterfaceDef if traits.flag.hasFlag(Modifier.Trait) => traits }.get
    val interface = tree.topDefs.collectFirst{ case traits: InterfaceDef if traits.flag.hasFlag(Modifier.Interface) => traits }.get

    val st = TypeTree(Ident("ST", pos), Vector.empty, Vector.empty, isPointer = false, pos)
    val mod = TypeTree(Ident("Mod", pos), Vector.empty, Vector.empty, isPointer = false, pos)

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
    val Apply(prefix, hargs, targs, args) = parseString(_.expr)((gen, tree) => gen.expr(tree)(file)) {
      """Int:::from(true)"""
    }

    val int = TypeTree(Ident("Int", pos), Vector.empty, Vector.empty, isPointer = false, pos)

    assert(hargs == Vector.empty)
    assert(targs == Vector.empty)
    assert(args == Vector(BoolLiteral(value = true, pos)))
    assert(prefix == StaticSelect(int, "from", pos))
  }

  test("parse top level method definition") {
    val filename = buildName(rootDir, filePath, "topLevelMethod.tchdl")
    val tree = parseFile(_.compilation_unit)((gen, tree) => gen(tree, filename))(filename).asInstanceOf[CompilationUnit]
  }

  test("parse generate stage") {
    parseString(_.generate)((gen, tree) => gen.generate(tree)(file)) {
      "generate s1(a, b) # st1(c, d)"
    }
  }

  test("parse type tree") {
    val tpe = parseString(_.`type`)((gen, tree) => gen.typeTree(tree)(file))_

    def tt(name: String) = TypeTree(Ident(name, pos), Vector.empty, Vector.empty, isPointer = false, pos)
    def ttPoly(name: String, hargs: Vector[HPExpr], targs: Vector[TypeTree]) = TypeTree(Ident(name, pos), hargs, targs, isPointer = false, pos)
    def cast(from: TypeTree, to: TypeTree): TypeTree = TypeTree(CastType(from, to, pos), Vector.empty, Vector.empty, isPointer = false, pos)
    def select(prefix: TypeTree, name: String): TypeTree = TypeTree(StaticSelect(prefix, name, pos), Vector.empty, Vector.empty, isPointer = false, pos)
    def pkg(name: String, pkg: String*) = TypeTree(SelectPackage(pkg.toVector, name, pos), Vector.empty, Vector.empty, isPointer = false, pos)

    val tree0 = tpe("A")
    val tree1 = tpe("A[1]")
    val tree2 = tpe("A[B]")
    val tree3 = tpe("A[m, B]")
    val tree4 = tpe("A as B")
    val tree5 = tpe("A as b:::B")
    val tree6 = tpe("A as B:::C")
    val tree7 = tpe("A:::B as C:::D")
    val tree8 = tpe("a:::A as B")
    val tree9 = tpe("A as (B:::C)")
    val tree10 = tpe("(A as B):::C as D")

    assert(tree0 == tt("A"))
    assert(tree1 == ttPoly("A", Vector(IntLiteral(1, pos)), Vector.empty))
    assert(tree2 == ttPoly("A", Vector.empty, Vector(tt("B"))))
    assert(tree3 == ttPoly("A", Vector(Ident("m", pos)), Vector(tt("B"))))
    assert(tree4 == cast(
      tt("A"),
      tt("B")
    ))

    assert(tree5 == cast(
      tt("A"),
      pkg("B", "b")
    ))


    assert(tree6 == cast(
      tt("A"),
      select(tt("B"), "C")
    ))


    assert(tree7 == cast(
      select(tt("A"), "B"),
      select(tt("C"), "D")
    ))

    assert(tree8 == cast(
      pkg("A", "a"),
      tt("B")
    ))

    assert(tree9 == cast(
      tt("A"),
      select(tt("B"), "C")
    ))

    assert(tree10 == cast(
      select(
        cast(tt("A"), tt("B")),
        "C"
      ),
      tt("D")
    ))
  }

  test("parse casting variable") {
    val expr = parseString(_.expr)((gen, tree) => gen.expr(tree)(file))_

    val tree0 = expr("(a as Int)")
    val tree1 = expr("(a as Int).f(2)")

    assert(tree0 == CastExpr(Ident("a", pos), TypeTree(Ident("Int", pos), Vector.empty, Vector.empty, isPointer = false, pos), pos))
    assert(tree1 == Apply(
      Select(
        CastExpr(Ident("a", pos), TypeTree(Ident("Int", pos), Vector.empty, Vector.empty, isPointer = false, pos), pos),
        "f",
        pos
      ),
      Vector.empty,
      Vector.empty,
      Vector(IntLiteral(2, pos)),
      pos
    ))
  }

  test("parse assign statement") {
    val assign = parseString(_.block_elem)((gen, tree) => gen.blockElem(tree)(Filename("")))_

    val tree0 = assign("this.a = 1")
    val tree1 = assign("this.mem.d = 2")
    val tree2 = assign("this.b = f(1, 2)")

    def select(head: String, name: String*): Select = {
      val headSelect = Select(This(pos), head, pos)

      name.foldLeft(headSelect) {
        case (accessor, name) => Select(accessor, name, pos)
      }
    }
    assert(tree0 == Assign(select("a"), IntLiteral(1, pos), pos))
    assert(tree1 == Assign(select("mem", "d"), IntLiteral(2, pos), pos))
    assert(tree2 == Assign(select("b"), Apply(Ident("f", pos), Vector.empty, Vector.empty, Vector(IntLiteral(1, pos), IntLiteral(2, pos)), pos), pos))
  }

  test("parse pointer type") {
    val parser = parseString(_.`type`)((gen, tree) => gen.typeTree(tree)(Filename("")))_

    val tree0 = parser("&Int")
    val tree1 = parser("&Bit[4]")
    val tree2 = parser("&Option[Int]")

    assert(tree0 == TypeTree(Ident("Int", pos), Vector.empty, Vector.empty, isPointer = true, pos))
    assert(tree1 == TypeTree(Ident("Bit", pos), Vector(IntLiteral(4, pos)), Vector.empty, isPointer = true, pos))
    assert(tree2 == TypeTree(Ident("Option", pos), Vector.empty, Vector(TypeTree(Ident("Int", pos), Vector.empty, Vector.empty, isPointer = false, pos)), isPointer = true, pos))
  }

  test("parse proc definition") {
    val parser = parseString(_.proc_def)((gen, tree) => gen.procDef(tree)(Filename("")))_
    val proc0 = parser("proc first @ 0b00 -> &Bit[2] {}")
    val proc1 = parser(
      """proc second @ 0b00 -> &Bit[2] {
        |  origin block a() {}
        |}
        |""".stripMargin
    )

    val retTpe = TypeTree(Ident("Bit", pos), Vector(IntLiteral(2, pos)), Vector.empty, isPointer = true, pos)
    val default = BitLiteral(0, 2, pos)
    val block = ProcBlock(
      Modifier("origin"),
      "a",
      Vector.empty,
      Block(Vector.empty, UnitLiteral(pos), pos),
      pos
    )

    assert(proc0 == ProcDef("first", retTpe, default, Vector.empty, pos))
    assert(proc1 == ProcDef("second", retTpe, default, Vector(block), pos))
  }

  test("parse commence procedure") {
    val parser = parseString(_.commence)((gen, tree) => gen.commence(tree)(Filename("")))_

    val com0 = parser("commence target # first()")
    val com1 = parser("commence target # first(0b00)")

    assert(com0 == Commence("target", CommenceBlock("first", Vector.empty, pos), pos))
    assert(com1 == Commence("target", CommenceBlock("first", Vector(BitLiteral(0, 2, pos)), pos), pos))
  }

  test("parse check for deref and multiply") {
    val parser = parseString(_.block)((gen, tree) => gen.block(tree)(Filename("")))_
    val blk = parser(
      """{
        |  val local = v0 * v1
        |  *pointer + local
        |}
        |""".stripMargin).asInstanceOf[Block]

    assert(blk.elems.length == 1)
    assert(blk.elems.head.isInstanceOf[ValDef])
    val localExpr = blk.elems.head.asInstanceOf[ValDef].expr.get
    assert(localExpr == StdBinOp(Operation.Mul, Ident("v0", pos), Ident("v1", pos), pos))
    assert(blk.last == StdBinOp(Operation.Add, DeReference(Ident("pointer", pos), pos), Ident("local", pos), pos))
  }
}
