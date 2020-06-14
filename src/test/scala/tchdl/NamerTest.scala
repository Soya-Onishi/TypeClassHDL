package tchdl

import org.scalatest.ParallelTestExecution
import tchdl.ast._
import tchdl.typecheck.Namer
import tchdl.util._

class NamerTest extends TchdlFunSuite {
  def parser(filename: String): AST = parseFile(_.compilation_unit)((gen, tree) => gen(tree, filename))(filename)

  test("named builtin") {
    implicit val global: GlobalData = new GlobalData

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

    val pkg = global.rootPackage.search(Vector("std", "types")) match {
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
