package tchdl.backend

import tchdl.backend.ast.{BackendLIR => lir}

import scala.annotation.tailrec

object PointerConnector {
  def exec(topTpe: BackendType, moduleList: Vector[lir.Module]): Vector[PointerConnection] = {
    val topPath = HWHierarchyPath(Vector.empty)
    val top = moduleList.find(_.tpe == topTpe).get

    val pointers = searchSources(top, moduleList, topPath)
    searchDestinations(pointers, top, moduleList)
  }

  private def searchSources(module: lir.Module, moduleList: Vector[lir.Module], path: HWHierarchyPath): Vector[PointerConnection] = {
    val pointers = module.components.collect { case pointer: lir.Pointer => pointer }
    val procNames = pointers.map(_.path.name.get).distinct
    val sources = procNames.map(path.add)
    val infos = sources.map(PointerConnection(_, Vector.empty))

    val memInfos = module.mems.map(mem => PointerConnection(path.add(mem.name), Vector.empty))
    val subModuleInfos = module.subs.flatMap{ sub =>
      val module = moduleList.find(_.tpe == sub.tpe).get
      val subPath = path.add(sub.name)
      searchSources(module, moduleList, subPath)
    }

    infos ++ memInfos ++ subModuleInfos
  }

  private def searchDestinations(pointers: Vector[PointerConnection], topModule: lir.Module, moduleList: Vector[lir.Module]): Vector[PointerConnection] = {
    def searchFirstRef(path: HWHierarchyPath): Vector[lir.Reference] = {
      val modulePath = HWHierarchyPath(path.path.init)
      val module = searchModule(modulePath, topModule, moduleList)
      val procName = path.path.last
      val stmts = module.components ++ module.inits ++ module.procedures

      def loop(stmts: Vector[lir.Stmt]): Vector[lir.Reference] = {
        val whens = stmts.collect{ case when: lir.When => when }
        val whenStmts = whens.flatMap(w => w.conseq ++ w.alt)

        val refs = stmts.collect{ case node: lir.Node => node }
          .collect{ case lir.Node(name, e: lir.Pointer, _) => (name, e) }
          .filter{ case (_, e) => e.path.name.get == procName }
          .map{ case (name, _) => lir.Reference(name, null) }

        refs ++ loop(whenStmts)
      }

      loop(stmts)
    }

    pointers
      .map(p => (p, searchFirstRef(p.source)))
      .map{ case (pointer, refs) =>
        val modulePath = HWHierarchyPath(pointer.source.path.init)
        val dsts = refs.flatMap(ref => searchConnection(
          ref,
          modulePath,
          searchModule(modulePath, topModule, moduleList),
          topModule,
          moduleList
        ))

        pointer.copy(dest = dsts)
      }
  }

  private def searchModule(path: HWHierarchyPath, top: lir.Module, moduleList: Vector[lir.Module]): lir.Module = {
    @tailrec def loop(path: Vector[String], module: lir.Module): lir.Module = path match {
      case Vector() => module
      case path =>
        val sub = module.subs.find(_.name == path.head).get
        val mod = moduleList.find(_.tpe == sub.tpe).get

        loop(path.tail, mod)
    }

    loop(path.path, top)
  }

  // ref   : reference of pointer as source
  // path  : module's path
  // module: current module
  //
  // return: deref pointer's path
  private def searchConnection(ref: lir.Ref, path: HWHierarchyPath, module: lir.Module, topModule: lir.Module, moduleList: Vector[lir.Module]): Vector[HWHierarchyPath] = {
    // TODO: current implementation is not exhaustive verification
    //       For example,
    //         node a.expr <= pointer(...)
    //              ^^^^^^  <-\
    //         node t <= a     ---- these are checked
    //                   ^  <-/
    //       is acceptable pattern, actually.
    @tailrec def isMatch(a: lir.Ref, b: lir.Ref): Boolean = (a, b) match {
      case (a: lir.Reference, b: lir.Reference) => a.name == b.name
      case (a: lir.SubField, b: lir.SubField) => a.name == b.name && isMatch(a.prefix, b.prefix)
      case (a: lir.SubIndex, b: lir.SubIndex) => a.idx == b.idx && isMatch(a.vec, b.vec)
      case (a: lir.SubAccess, b: lir.SubAccess) => isMatch(a.vec, b.vec)
      case _ => false
    }

    @tailrec def nextPath(ref: lir.Ref): HWHierarchyPath = {
      ref match {
        case ref: lir.SubField => nextPath(ref.prefix)
        case ref: lir.SubAccess => nextPath(ref.vec)
        case ref: lir.SubIndex => nextPath(ref.vec)
        case lir.Reference(name, _) =>
          val isSub = module.subs.exists(_.name == name)
          val isPort = module.ports.exists(_.name == name)

          if(isSub) path.add(name)
          else if(isPort) HWHierarchyPath(path.path.init)
          else path
      }
    }

    def searchNext(stmt: lir.Stmt): Vector[(lir.Ref, HWHierarchyPath)] = stmt match {
      case lir.Reg(name, Some(default), _) if isMatch(default, ref) =>
        Vector((lir.Reference(name, null), path))
      case t: lir.Assign if isMatch(t.src, ref) =>
        Vector((t.dst, nextPath(ref)))
      case t: lir.When =>
        t.conseq.flatMap(searchNext) ++ t.alt.flatMap(searchNext)
      case t: lir.Node =>
        t.src match {
          case srcRef: lir.Ref if isMatch(srcRef, ref) =>
            Vector((lir.Reference(t.name, null), path))
          case _                                       =>
            Vector.empty
        }
      case _ => Vector.empty
    }

    def searchDeref(stmt: lir.Stmt): Vector[HWHierarchyPath] = stmt match {
      case t: lir.Node => t.src match {
        case deref: lir.Deref if isMatch(deref.expr, ref) => Vector(path.add(t.name))
        case _ => Vector.empty
      }
      case t: lir.When => t.conseq.flatMap(searchDeref) ++ t.alt.flatMap(searchDeref)
    }

    val stmts = module.components ++ module.inits ++ module.procedures
    val nextRefs = stmts.flatMap(searchNext)
    val derefs = stmts.flatMap(searchDeref)

    val dsts = nextRefs.flatMap{
      case (ref, path) =>
        val nextModule = searchModule(path, topModule, moduleList)
        searchConnection(ref, path, nextModule, topModule, moduleList)
    }

    derefs ++ dsts
  }
}

case class HWHierarchyPath(path: Vector[String]) {
  def add(name: String): HWHierarchyPath = this.copy(path = this.path :+ name)
}
case class PointerConnection(
  source: HWHierarchyPath,
  dest: Vector[HWHierarchyPath]
)

