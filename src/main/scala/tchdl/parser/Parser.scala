package tchdl.parser

import org.antlr.v4.runtime._
import tchdl.antlr._
import tchdl.util.TchdlException.ImplementationErrorException

import scala.util.Try


object Parser {
  def parse(filename: String) = {
    val input = Try(CharStreams.fromFileName(filename)).toEither match {
      case Right(input) => input
      case Left(exception) => throw new ImplementationErrorException(exception.toString)
    }

    val lexer= new TchdlLexer(input)
    val tokens = new CommonTokenStream(lexer)
    val parser = new TchdlParser(tokens)
    val tree = parser.compilation_unit()

    val generator = new ASTGenerator
    generator(tree, filename)
  }
}
