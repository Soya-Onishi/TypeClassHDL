package tchdl

import tchdl.ast._
import tchdl.util.{Modifier, Context, Symbol}
import tchdl.typecheck.SymbolMaker
import org.scalatest.funsuite.AnyFunSuite

class SymbolMakerTest extends AnyFunSuite {
  test("make struct symbol") {
    val tree = StructDef(
      "Test",
      Vector(),
      Vector(),
      Vector(),
      Vector(
        ValDef(Modifier.NoExpr, "field", Some(TypeTree("Int", Vector(), Vector())), None)
      )
    )

    SymbolMaker.makeSymbol(tree, Context.root(Vector())).symbol match {
      case symbol: Symbol.TypeSymbol =>
        assert(symbol.name == "Test")
        assert(symbol.namespace == Vector())
        assert(symbol.getOwner.isEmpty)
      case symbol =>
        fail(s"expected TypeSymbol actual: ${symbol.getClass}")
    }
  }

  test("make method symbol") {
    val tree = MethodDef(
      "method",
      Vector(),
      Vector(),
      Vector(),
      Vector(),
      TypeTree("Int", Vector(), Vector()),
      Some(Block(Vector(), UnitLiteral()))
    )

    SymbolMaker.makeSymbol(tree, Context.root(Vector())).symbol match {
      case symbol: Symbol.TermSymbol =>
        assert(symbol.name == "method")
        assert(symbol.namespace == Vector())
        assert(symbol.getOwner.isEmpty)
        assert(symbol.hasFlag(Modifier.Method))
      case _ =>
        fail("expected TermSymbol")
    }
  }
}
