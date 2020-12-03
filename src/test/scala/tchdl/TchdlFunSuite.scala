package tchdl

import tchdl.parser.ASTGenerator
import tchdl.ast._
import tchdl.antlr._
import tchdl.util._
import tchdl.backend.ast.{BackendLIR => lir}
import tchdl.backend._
import tchdl.parser._

import org.antlr.v4.runtime._
import org.antlr.v4.runtime.tree._
import java.nio.file.Paths

import scala.reflect.ClassTag
import scala.reflect.runtime.universe.TypeTag
import org.scalatest.funsuite.AnyFunSuite

class TchdlFunSuite extends AnyFunSuite {
  val rootDir: String = Paths.get(".").toAbsolutePath.normalize.toString
  val builtinPath: String = "src/test/builtin"
  val filePath: String = "src/test/files"
  val builtinTypes: String = buildName(rootDir, builtinPath, "types.tchdl")
  val builtinTraits: String = buildName(rootDir, builtinPath, "traits.tchdl")
  val builtinInterfaces: String = buildName(rootDir, builtinPath, "interfaces.tchdl")
  val builtinFunctions: String = buildName(rootDir, builtinPath, "functions.tchdl")
  val builtInFiles: Vector[String] = Vector(builtinTypes, builtinTraits, builtinInterfaces, builtinFunctions)

  def parseString[T <: ParseTree](parsing: TchdlParser => T)(ast: (ASTGenerator, T) => AST)(code: String): AST =
    parseInput(parsing)(ast)(CharStreams.fromString(code))

  def parseFile[T <: ParseTree](parsing: TchdlParser => T)(ast: (ASTGenerator, T) => AST)(filename: String): AST =
    parseInput(parsing)(ast)(CharStreams.fromFileName(filename))

  def parseInput[T <: ParseTree](parsing: TchdlParser => T)(ast: (ASTGenerator, T) => AST)(input: CharStream): AST = {
    val lexer= new TchdlLexer(input)
    val tokens = new CommonTokenStream(lexer)
    val parser = new TchdlParser(tokens)
    val tree = parsing(parser)
    val errors = parser.getNumberOfSyntaxErrors

    if(errors > 0) throw new AssertionError("parse error occured")
    else ast(new ASTGenerator, tree)
  }

  def buildName(path: String*): String = path.mkString("/")

  def showErrors(global: GlobalData): String =
    global.repo.error.elems.map(_.debugString).mkString("\n\n")

  def expectNoError(implicit global: GlobalData): Unit = {
    expectError(0)
  }

  def expectError(count: Int)(implicit global: GlobalData): Unit = {
    assert(global.repo.error.counts == count, showErrors(global))
  }

  def showErrorsSimple(implicit global: GlobalData): String =
    global.repo.error.elems.map(_.toString).mkString("\n")

  def findModule(modules: Vector[lir.Module], tpeStr: String): Option[lir.Module] = {
    def isSameTpe(tpe: BackendType, tpeTree: TypeTree): Boolean = {
      def toHPElem(harg: HPExpr): HPElem = harg match {
        case IntLiteral(value) => HPElem.Num(value)
        case StringLiteral(str) => HPElem.Str(str)
        case _ => ???
      }

      val TypeTree(Ident(tpeName), hps, tps, _) = tpeTree

      def isSameName = tpe.symbol.name == tpeName
      def isSameHPLen = tpe.hargs.length == hps.length
      def isSameHPElem = tpe.hargs == hps.map(toHPElem)
      def isSameTPLen = tpe.targs.length == tps.length
      def isSameTPElem = (tpe.targs zip tps).forall{ case (t0, t1) => isSameTpe(t0, t1) }

      isSameName && isSameHPLen && isSameTPLen && isSameHPElem && isSameTPElem
    }

    val parser = parseString(_.`type`)((gen, tree) => gen.typeTree(tree)(Filename("")))_
    val tpeTree = parser(tpeStr).asInstanceOf[TypeTree]

    modules.find(mod => isSameTpe(mod.tpe, tpeTree))
  }

  def findAllComponents[T: ClassTag : TypeTag](stmts: Vector[lir.Stmt]): Vector[T] = {
    if(stmts.isEmpty) Vector.empty
    else {
      val nodes = stmts.collect{ case n: T => n }
      val whens = stmts.collect{ case w: lir.When => w }
      val conseqs = findAllComponents(whens.flatMap(_.conseq))
      val alts = findAllComponents(whens.flatMap(_.alt))

      nodes ++ conseqs ++ alts
    }
  }
}
