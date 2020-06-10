package tchdl

import tchdl.ast._
import tchdl.typecheck.Namer
import tchdl.util._

import org.scalatest.funsuite.AnyFunSuite
import java.nio.file.Paths

class NamerTest extends AnyFunSuite {
  val rootDir: String = Paths.get(".").toAbsolutePath.normalize.toString
  val builtinPath: String = "src/test/builtin"

  val builtinTypes: String = Seq(rootDir, builtinPath, "types.tchdl").mkString("/")
  def parser(filename: String): AST = parseFile(_.compilation_unit)((gen, tree) => gen(tree, filename))(filename)

  test("named builtin") {
    def lookupStruct(name: String, ctx: Context): Unit = {
      ctx.lookup[Symbol](name) match {
        case LookupResult.LookupFailure(err) => fail(s"lookup failed: err is [$err]")
        case LookupResult.LookupSuccess(symbol) =>
          assert(symbol.path.pkgName == Vector("std", "types"))
          assert(symbol.path.name.isDefined)
          assert(symbol.path.name.get == name)
          assert(symbol.isInstanceOf[Symbol.EntityTypeSymbol])
      }
    }

    val tree = parser(builtinTypes).asInstanceOf[CompilationUnit]
    Namer.exec(tree)

    val pkg = Symbol.RootPackageSymbol.search(Vector("std", "types")) match {
      case Left(name) => fail(s"$name does not here")
      case Right(pkg) => pkg
    }

    val ctx = pkg.lookupCtx(builtinTypes).getOrElse(fail(s"context($builtinTypes) must be here"))
    val types = Seq(
      "Int",
      "String",
      "Bit",
      "Unit",
      "Num",
      "Str"
    )

    types.foreach(lookupStruct(_, ctx))
  }
}