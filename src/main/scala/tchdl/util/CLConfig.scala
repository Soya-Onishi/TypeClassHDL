package tchdl.util

import tchdl.ast._
import tchdl.parser._
import tchdl.antlr._
import org.antlr.v4.runtime.{Parser => _, _}
import scopt.OParser
import scala.collection.JavaConverters._
import java.io.File
import java.nio.file.{Path, Paths, Files}

case class CLConfig(
  filenames: Seq[String],
  topModulePkg: Vector[String],
  topModule: Option[TypeTree],
  output: Path,
  outputDir: Path,
  frontendOnly: Boolean,
  outputFir: Boolean,
)

object CommandLineParser {
  private val errors = Seq.newBuilder[CLError]
  private val parser = {
    val builder = OParser.builder[CLConfig]
    import builder._

    OParser.sequence(
      programName("Spiral Compiler"),
      head("Spiral Compiler", "0.0.1"),
      opt[String]("<file>...")
        .unbounded()
        .action((x, c) => c.copy(filenames = c.filenames :+ x)),
      opt[String]("package")
        .valueName("<package name>")
        .action((x, c) => c.copy(topModulePkg = parsePkgName(x)))
        .text("package name of top module"),
      opt[String]("top")
        .valueName("<module type>")
        .action((x, c) => c.copy(topModule = parseTopModule(x)))
        .text("top module type"),
      opt[File]('o', "out")
        .valueName("<file>")
        .optional()
        .action((x, c) => c.copy(output = x.toPath))
        .text("output file name"),
      opt[File]("target-dir")
        .valueName("<dir>")
        .optional()
        .action((x, c) => c.copy(outputDir = x.toPath))
        .text("output target directory"),
      opt[Unit]("out-fir")
        .action((_, c) => c.copy(outputFir = true))
        .text("output firrtl file instead of verilog"),
      opt[Unit]("frontend")
        .action((_, c) => c.copy(frontendOnly = true))
        .text("run only frontend not to generate any files"),
      help("help").text("prints this usage text"),
      checkConfig { c =>
        if(c.filenames.isEmpty) {
          errors += CLNoFileNames
        }

        c.filenames
          .filterNot(file => Paths.get(file).toFile.exists())
          .foreach(file => errors += CLFileNotExist(file))

        if(!c.frontendOnly && c.topModule.isEmpty && c.topModulePkg.isEmpty) {
          errors += CLRequireTopModule
        }
        if(Files.notExists(c.outputDir)) {
          errors += CLOutputDirNotExists(c.outputDir.toString)
        }
        if(!Files.isDirectory(c.outputDir)) {
          errors += CLOutputDirNotDirectory(c.outputDir.toString)
        }

        val errs = errors.result()
        if(errs.isEmpty) success
        else failure(errs.map(_.toString + "\n").mkString(""))
      }
    )
  }

  private def parseTopModule(tpe: String): Option[TypeTree] = {
    val input = CharStreams.fromString(tpe)
    val lexer= new TchdlLexer(input)
    val tokens = new CommonTokenStream(lexer)
    val parser = new TchdlParser(tokens)
    val tree = parser.`type`()

    val generator = new ASTGenerator
    val typeTree = generator.typeTree(tree)(Filename(""))

    if(parser.getNumberOfSyntaxErrors == 0) Some(typeTree)
    else {
      errors += CLTypeParseError(tpe)
      None
    }
  }

  private def parsePkgName(pkgName: String): Vector[String] = {
    val pkgString = s"package $pkgName"

    val input = CharStreams.fromString(pkgString)
    val lexer= new TchdlLexer(input)
    val tokens = new CommonTokenStream(lexer)
    val parser = new TchdlParser(tokens)
    val tree = parser.pkg_name()

    if(parser.getNumberOfSyntaxErrors == 0) tree.EXPR_ID.asScala.map(_.getText).toVector
    else {
      errors += CLPackageParseError(pkgName)
      Vector.empty
    }
  }

  def parse(args: Array[String]): Option[CLConfig] = {
    val config = CLConfig(
      filenames = Seq.empty,
      topModulePkg = Vector.empty,
      topModule = Option.empty,
      output = Paths.get("out.v"),
      outputDir = Paths.get("."),
      frontendOnly = false,
      outputFir = false,
    )

    OParser.parse(parser, args, config)
  }
}

trait CLError
case object CLNoFileNames extends CLError
case class  CLFileNotExist(filename: String) extends CLError
case object CLRequireTopModule extends CLError
case class CLTypeParseError(tpe: String) extends CLError
case class CLPackageParseError(pkg: String) extends CLError
case class CLOutputDirNotExists(dir: String) extends CLError
case class CLOutputDirNotDirectory(dir: String) extends CLError
