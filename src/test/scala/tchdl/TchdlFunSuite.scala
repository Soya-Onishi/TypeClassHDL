package tchdl

import tchdl.parser.ASTGenerator
import tchdl.ast._
import tchdl.antlr._
import tchdl.util._
import org.antlr.v4.runtime._
import org.antlr.v4.runtime.tree._
import java.nio.file.Paths

import org.scalatest.funsuite.AnyFunSuite

class TchdlFunSuite extends AnyFunSuite {
  val rootDir: String = Paths.get(".").toAbsolutePath.normalize.toString
  val builtinPath: String = "src/test/builtin"
  val filePath: String = "src/test/files"
  val builtinTypes: String = buildName(rootDir, builtinPath, "types.tchdl")
  val builtinTraits: String = buildName(rootDir, builtinPath, "traits.tchdl")
  val builtinInterfaces: String = buildName(rootDir, builtinPath, "interfaces.tchdl")
  val builtInFiles: Vector[String] = Vector(builtinTypes, builtinTraits, builtinInterfaces)

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
}
