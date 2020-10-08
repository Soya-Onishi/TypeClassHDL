package tchdl

import tchdl.ast._
import tchdl.backend.ast.{BackendLIR => lir}
import tchdl.util._
import tchdl.typecheck._
import tchdl.parser._
import tchdl.backend._

import firrtl.{ir => fir}

class FirrtlCodeGenTest extends TchdlFunSuite {
  def parse(filename: String): CompilationUnit =
    parseFile(_.compilation_unit)((gen, tree) => gen(tree, filename))(filename).asInstanceOf[CompilationUnit]

  def untilThisPhase(pkgName: Vector[String], module: String, names: String*): (fir.Circuit, GlobalData) = {
    val fullnames = names.map(buildName(rootDir, filePath, _))
    val filenames = fullnames ++ builtInFiles

    val trees = filenames.map(parse)
    val moduleTree = parseString(_.`type`)((gen, tree) => gen.typeTree(tree)(Filename("")))(module).asInstanceOf[TypeTree]
    implicit val global: GlobalData = GlobalData(pkgName, moduleTree)

    trees.foreach(Namer.exec)
    expectNoError

    trees.foreach(NamerPost.exec)
    expectNoError

    trees.foreach(BuildImplContainer.exec)
    expectNoError

    VerifyImplConflict.verifyImplConflict()
    expectNoError

    val trees0 = trees.map(TopDefTyper.exec)
    expectNoError

    trees0.foreach(ImplMethodSigTyper.exec)
    expectNoError

    val trees1 = trees0.map(Typer.exec)
    expectNoError

    trees1.foreach(RefCheck.exec)
    expectNoError

    val newGlobal = global.assignCompilationUnits(trees1.toVector)
    val modules = BuildGeneratedModuleList.exec(newGlobal)
    expectNoError(newGlobal)

    val (moduleContainers, methodContainers) = BackendIRGen.exec(modules)(newGlobal)
    expectNoError(newGlobal)

    val lirModules = BackendLIRGen.exec(moduleContainers, methodContainers)
    val topModuleTpe = moduleContainers.head.tpe
    val connections = PointerConnector.exec(topModuleTpe, lirModules)

    val topModule = lirModules.find(_.tpe == topModuleTpe).get
    val circuit = FirrtlCodeGen.exec(topModule, lirModules, connections)(newGlobal)

    (circuit, newGlobal)
  }

  test("simple code") {
    val (circuit, _) = untilThisPhase(Vector("test"), "Top[8]", "OnlyTopThrowWire.tchdl")
    val modules = circuit.modules.collect{ case m: fir.Module => m }

    assert(modules.length == 1)

    val top = modules.head
    val stmts = top.body.asInstanceOf[fir.Block].stmts
    val whens = stmts.collect{ case w: fir.Conditionally => w }

    assert(whens.length == 1)

    val when = whens.head
    assert(when.pred.isInstanceOf[fir.Reference])
    val active = when.pred.asInstanceOf[fir.Reference]
    assert(active.name.matches("function_[0-9a-f]+\\$_active"))
    assert(top.ports.exists(_.name == active.name))
    val conseq = when.conseq.asInstanceOf[fir.Block].stmts
    val connects = conseq.collect{ case c: fir.Connect => c }
    assert(connects.length == 1)
    val connect = connects.head

    val dst = connect.loc.asInstanceOf[fir.Reference]
    val src = connect.expr.asInstanceOf[fir.Reference]

    assert(dst.name.matches("function_[0-9a-f]+\\$_ret"))
    assert(src.name.matches("function_[0-9a-f]+\\$in"), src.name)
  }

  test("use proc and deref") {
    val (circuit, _) = untilThisPhase(Vector("test"), "UseDeref", "procDeref.tchdl")
    val modules = circuit.modules.collect{ case m: fir.Module => m }
    val top = modules.head
    val stmts = top.body.asInstanceOf[fir.Block].stmts
    val whens = stmts.collect{ case w: fir.Conditionally => w }

    assert(whens.length == 3)

    val exec = whens.find{ when =>
      val ref = when.pred.asInstanceOf[fir.Reference]
      ref.name.matches("exec_[0-9a-f]+\\$_active")
    }.get

    val conseq = exec.conseq.asInstanceOf[fir.Block].stmts
    val connects = conseq.collect{ case c: fir.Connect => c }
    val connect = connects.find(_.loc.asInstanceOf[fir.Reference].name.matches("exec_[0-9a-f]+\\$_ret")).get
    val srcName = connect.expr.asInstanceOf[fir.Reference].name
    val nodes = exec.conseq.asInstanceOf[fir.Block].stmts.collect{ case n: fir.DefNode => n }
    val primNode = nodes.find(_.name == srcName).get

    val doPrim = primNode.value.asInstanceOf[fir.DoPrim]
    assert(doPrim.op == firrtl.PrimOps.Add)
    val arg = doPrim.args.head.asInstanceOf[fir.Reference]

    val argNode = nodes.find(_.name == arg.name).get
    val betweenRef = argNode.value.asInstanceOf[fir.Reference]
    val pointerNode = nodes.find(_.name == betweenRef.name).get

    assert(pointerNode.value.asInstanceOf[fir.Reference].name == "__pointer_0")

    val multCycleBlock = whens(2).conseq.asInstanceOf[fir.Block].stmts
    val whenConnect = multCycleBlock.collectFirst{ case c: fir.Conditionally => c }.get
    val pointerConnect = whenConnect.conseq.asInstanceOf[fir.Connect]

    pointerConnect.expr.asInstanceOf[fir.Reference].name.matches("multCycle_[0-9a-f]+_next\\$result")
  }
}
