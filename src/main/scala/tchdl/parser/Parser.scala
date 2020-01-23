package tchdl.parser

import tchdl.ast._
import org.antlr.v4.runtime._
import org.antlr.v4.runtime.tree._
import tchdl.antlr._
import java.io.FileInputStream

object Parser {
  def parse(filename: String) = {
    val input = CharStreams.fromFileName(filename)
    val lexer= new TchdlLexer(input)
    val tokens = new CommonTokenStream(lexer)
    val parser = new TchdlParser(tokens)
    val tree = parser.compilation_unit()

    val generator = new ASTGenerator
    generator(tree, filename)
  }
}
