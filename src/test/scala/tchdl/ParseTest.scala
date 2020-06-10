package tchdl

import tchdl.parser.ASTGenerator
import tchdl.ast._
import tchdl.antlr._
import tchdl.util._

import org.antlr.v4.runtime._
import org.antlr.v4.runtime.tree._
import org.scalatest.funsuite.AnyFunSuite

class ParseTest extends AnyFunSuite {
  def parseString[T <: ParseTree](parsing: TchdlParser => T)(ast: (ASTGenerator, T) => AST)(code: String): AST =
    parseInput(parsing)(ast)(CharStreams.fromString(code))

  def parseFile[T <: ParseTree](parsing: TchdlParser => T)(ast: (ASTGenerator, T) => AST)(filename: String): AST =
    parseInput(parsing)(ast)(CharStreams.fromFileName(filename))

  def parseInput[T <: ParseTree](parsing: TchdlParser => T)(ast: (ASTGenerator, T) => AST)(input: CharStream): AST = {
    val lexer= new TchdlLexer(input)
    val tokens = new CommonTokenStream(lexer)
    val parser = new TchdlParser(tokens)
    val tree = parsing(parser)
    ast(new ASTGenerator, tree)
  }

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
          Vector.empty
        )
    )
  }
}
