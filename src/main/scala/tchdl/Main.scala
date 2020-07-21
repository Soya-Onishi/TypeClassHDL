package tchdl

import tchdl.util._
import tchdl.parser._
import tchdl.ast.TypeTree
import tchdl.antlr._
import tchdl.typecheck._
import tchdl.backend._

import org.antlr.v4.runtime.{Parser => _, _}

import scala.collection.JavaConverters._
import java.nio.file._

object Main extends App {
  def parseCommand(commands: Vector[String]): Command = {
    def getTopModule(tpe: String): Either[Error, TypeTree] = {
      val input = CharStreams.fromString(tpe)
      val lexer= new TchdlLexer(input)
      val tokens = new CommonTokenStream(lexer)
      val parser = new TchdlParser(tokens)
      val tree = parser.`type`()

      val generator = new ASTGenerator
      val typeTree = generator.typeTree(tree)

      if(parser.getNumberOfSyntaxErrors == 0) Right(typeTree)
      else Left(???)
    }

    def getPkgName(pkgName: String): Either[Error, Vector[String]] = {
      val pkgString = s"package $pkgName"

      val input = CharStreams.fromString(pkgString)
      val lexer= new TchdlLexer(input)
      val tokens = new CommonTokenStream(lexer)
      val parser = new TchdlParser(tokens)
      val tree = parser.pkg_name()

      if(parser.getNumberOfSyntaxErrors > 0) Left(???)
      else {
        val pkg = tree.EXPR_ID.asScala.map(_.getText).toVector
        Right(pkg)
      }
    }

    def loop(remains: Vector[String]): Command = {
      remains.headOption match {
        case Some("--pkg") =>
          val result = remains.tail.headOption match {
            case None => Left(???)
            case Some(pkg) => getPkgName(pkg)
          }

          result match {
            case Left(err) => ???
            case Right(pkg) => loop(remains.tail.tail).copy(topModulePkg = pkg)
          }
        case Some("--top") =>
          val result = remains.tail.headOption match {
            case None => Left(???)
            case Some(tpe) => getTopModule(tpe)
          }

          result match {
            case Left(err) => ???
            case Right(tpeTree) => loop(remains.tail.tail).copy(topModule = Some(tpeTree))
          }
        case Some("--stdlib") =>
          remains.tail.headOption match {
            case None => ???
            case Some(libdir) => loop(remains.tail.tail).copy(stdlibDir = libdir)
          }
        case Some(filename) =>
          val com = loop(remains.tail)
          com.copy(filenames = com.filenames :+ filename)
        case None => Command.empty
      }
    }

    loop(commands)
  }

  val command = parseCommand(args.tail.toVector)
  val stdlibFiles = Vector("types.tchdl", "functions.tchdl", "traits.tchdl", "interfaces.tchdl").map(Paths.get(command.stdlibDir, _))
  val filenames = command.filenames ++ stdlibFiles
  val compilationUnits = command.filenames.map(Parser.parse)
  val global = GlobalData(command)
  compilationUnits.foreach(Namer.exec(_)(global))
  compilationUnits.foreach(NamerPost.exec(_)(global))
  compilationUnits.foreach(BuildImplContainer.exec(_)(global))
  VerifyImplConflict.verifyImplConflict()(global)
  val trees0 = compilationUnits.map(TopDefTyper.exec(_)(global))
  trees0.foreach(ImplMethodSigTyper.exec(_)(global))
  val trees1 = trees0.map(Typer.exec(_)(global))
  trees1.foreach(RefCheck.exec(_)(global))
  val newGlobal = global.assignCompilationUnits(trees1)
  val modules = BuildGeneratedModuleList.exec(newGlobal)
  val (moduleContainers, methodContainers) = BackendIRGen.exec(modules)(newGlobal)
  val topModule = moduleContainers.head.tpe
  val circuit = FirrtlCodeGen.exec(topModule, moduleContainers, methodContainers)(newGlobal)

  Files.writeString(Paths.get("out.fir"), circuit.serialize)
}
