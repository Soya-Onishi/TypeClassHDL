package tchdl

import firrtl.stage.FirrtlStage
import tchdl.util._
import tchdl.parser._
import tchdl.ast.{CompilationUnit, TypeTree}
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
      val typeTree = generator.typeTree(tree)(Filename(""))

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
        case Some("--output") =>
          remains.tail.headOption match {
            case None => ???
            case Some(filename) => loop(remains.tail.tail).copy(output = Some(filename))
          }
        case Some(filename) =>
          val com = loop(remains.tail)
          com.copy(filenames = com.filenames :+ filename)
        case None => Command.empty
      }
    }

    loop(commands)
  }

  def showError(global: GlobalData): Unit =
    if(global.repo.error.counts != 0) {
      println(global.repo.error.elems.mkString("\n"))
      System.exit(1)
    }

  def frontend(phases: Seq[(Seq[CompilationUnit], GlobalData) => Seq[CompilationUnit]]): Either[Seq[Error], (Seq[CompilationUnit], GlobalData)] = {
    val cus = filenames.map(Parser.parse)
    val global = GlobalData(config)

    def runPhases(
      phases: Seq[(Seq[CompilationUnit], GlobalData) => Seq[CompilationUnit]],
      cus: Seq[CompilationUnit],
      global: GlobalData
    ): Either[Seq[Error], (Seq[CompilationUnit], GlobalData)] = {
      phases.headOption match {
        case None => Right((cus, global))
        case Some(phase) =>
          val nextCUs = phase(cus, global)
          val nextGlobal = global.assignCompilationUnits(nextCUs)

          if(global.repo.error.counts == 0) runPhases(phases.tail, nextCUs, nextGlobal)
          else                              Left(global.repo.error.elems)
      }
    }

    runPhases(phases, cus, global)
  }

  def backend[T](phase: GlobalData => T)(global: GlobalData): Either[Seq[Error], T] = {
    val result = phase(global)

    if(global.repo.error.counts == 0) Right(result)
    else Left(global.repo.error.elems)
  }

  val config = CommandLineParser.parse(args).getOrElse(sys.exit(1))
  val stdlibPath = sys.env.getOrElse("SPIRAL_STDLIB_PATH", {
    Console.err.println("Need to set environment variable: SPIRAL_STD_LIB_PATH")
    sys.exit(1)
  })
  val stdlibDir = Paths.get(stdlibPath).toFile
  if(!stdlibDir.isDirectory) {
    Console.err.println(s"SPIRAL_STDLIB_PATH's path is not directory. $stdlibDir")
    sys.exit(1)
  }
  if(!stdlibDir.exists()) {
    Console.err.println(s"SPIRAL_STDLIB_PATH's path does not exist. $stdlibDir")
    sys.exit(1)
  }

  val stdlibFiles = Seq(
    "types.tchdl",
    "functions.tchdl",
    "traits.tchdl",
    "interfaces.tchdl"
  ).map(name => Paths.get(stdlibPath, name).toString)

  val filenames = config.filenames ++ stdlibFiles

  val global = GlobalData(config)
  val compilationUnits = filenames.map{ name =>
    println(s"parsing $name...")
    Parser.parse(name)
  }

  println("compilation running...")
  val frontendResult = frontend(Seq(
    (cus, global) => cus.map(Namer.exec(_)(global)),
    (cus, global) => cus.map(NamerPost.exec(_)(global)),
    (cus, global) => cus.map(BuildImplContainer.exec(_)(global)),
    (cus, global) => { VerifyImplConflict.verifyImplConflict()(global); cus },
    (cus, global) => cus.map(TopDefTyper.exec(_)(global)),
    (cus, global) => cus.map(ImplMethodSigTyper.exec(_)(global)),
    (cus, global) => cus.map(Typer.exec(_)(global)),
    (cus, global) => cus.map(RefCheck.exec(_)(global)),
  ))

  println("generating output products...")

  val result = frontendResult match {
    case Left(errors) => Left(errors)
    case Right((_, global)) =>
      for {
        modules <- backend(global => BuildGeneratedModuleList.exec(global))(global)
        container <- backend(global => BackendIRGen.exec(modules)(global))(global)
        (moduleContainers, methodContainers) = container
        lirModules = BackendLIRGen.exec(moduleContainers, methodContainers)(global)
        lirTopTpe = moduleContainers.head.tpe
        connections = PointerConnector.exec(lirTopTpe, lirModules)(global)
        topModule = lirModules.find(_.tpe == lirTopTpe).get
        firCircuit = FirrtlCodeGen.exec(topModule, lirModules, connections)(global)
      } yield firCircuit
  }

  result match {
    case Left(errors) => Console.err.println(errors.mkString("\n\n"))
    case Right(circuit) =>
      val outputName = config.output.toString
      val outputDir = config.outputDir.toAbsolutePath.toString
      val outputPath = Paths.get(outputDir, outputName)

      println("run firrtl...")

      val annons = Seq(
        firrtl.stage.FirrtlCircuitAnnotation(circuit),
        firrtl.stage.OutputFileAnnotation(outputPath.toString)
      )
      val options = Array("-X", "verilog", "--no-dce")
      (new FirrtlStage).execute(options, annons)
  }

  /*
  compilationUnits.foreach(Namer.exec(_)(global))
  showError(global)

  compilationUnits.foreach(NamerPost.exec(_)(global))
  showError(global)

  compilationUnits.foreach(BuildImplContainer.exec(_)(global))
  showError(global)

  VerifyImplConflict.verifyImplConflict()(global)
  showError(global)

  val trees0 = compilationUnits.map(TopDefTyper.exec(_)(global))
  showError(global)

  trees0.foreach(ImplMethodSigTyper.exec(_)(global))
  showError(global)

  val trees1 = trees0.map(Typer.exec(_)(global))
  showError(global)

  trees1.foreach(RefCheck.exec(_)(global))
  showError(global)
  */

  /*
  val newGlobal = global.assignCompilationUnits(trees1)
  val modules = BuildGeneratedModuleList.exec(newGlobal)
  showError(global)

  val (moduleContainers, methodContainers) = BackendIRGen.exec(modules)(newGlobal)
  showError(global)

  val topModule = moduleContainers.head.tpe
  val lirModule = BackendLIRGen.exec(moduleContainers, methodContainers)(newGlobal)
  showError(global)

  val output = command.output.getOrElse("out.fir")
  // Files.writeString(Paths.get(output), circuit.serialize)
 */
}
