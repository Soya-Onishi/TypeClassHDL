package tchdl

import tchdl.ast._
import tchdl.util._

import org.scalatest.funsuite.AnyFunSuite
import java.nio.file.Paths

class ParseTest extends AnyFunSuite {
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
      ValDef(Modifier.NoModifier, name, Some(tpe), None)

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
        Vector(ValDef(Modifier.Parent, "p", Some(TypeTree(Ident("M1"), Vector.empty, Vector.empty)), None)),
        Vector(ValDef(Modifier.Sibling, "s", Some(TypeTree(Ident("M2"), Vector.empty, Vector.empty)), None)),
      )
    )

    assert(
      parser("module Mod[m: Num, T] where m: min 1 & max 3, T: I0 + I1") ==
      ModuleDef (
        "Mod",
        Vector(ValDef(Modifier.NoModifier, "m", Some(TypeTree(Ident("Num"), Vector.empty, Vector.empty)), None)),
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
          "f",
          Vector.empty,
          Vector.empty,
          Vector.empty,
          Vector.empty,
          TypeTree(Ident("Unit"), Vector.empty, Vector.empty),
          Some(Block(Vector.empty, UnitLiteral()))
        )),
        Vector.empty
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
        Vector(ValDef(Modifier.NoModifier, "m", Some(TypeTree(Ident("Num"), Vector.empty, Vector.empty)), None)),
        Vector(TypeDef("T")),
        Vector.empty,
        Vector.empty
      )
    )
  }

  test("parse builtin types") {
    val filename = "src/test/builtin/types.tchdl"
    val root = Paths.get(".").toAbsolutePath.normalize().toString
    val path = Seq(root, filename).mkString("/")

    parseFile(_.compilation_unit)((gen, tree) => gen(tree, path))(path)
  }
}
