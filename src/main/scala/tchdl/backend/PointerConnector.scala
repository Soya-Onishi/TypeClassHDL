package tchdl.backend

import tchdl.backend.ast.{BackendLIR => lir}
import tchdl.util.TchdlException.ImplementationErrorException

import scala.annotation.tailrec

object PointerConnector {
  def exec(topTpe: BackendType, moduleList: Vector[lir.Module]): Vector[PointerConnection] = {
    val top = moduleList.find(_.tpe == topTpe).get

    val (pointers, _) = searchSources(top, moduleList, Vector.empty, 0)
    searchDestinations(pointers, top, moduleList)
  }

  private def searchSources(module: lir.Module, moduleList: Vector[lir.Module], modulePath: Vector[String], id: Int): (Vector[PointerConnection], Int) = {
    def findNodes(stmts: Vector[lir.Stmt]): Vector[lir.Node] = {
      val nodes = stmts.collect{ case n: lir.Node => n }
      val whens = stmts.collect{ case w: lir.When => w }

      nodes ++ findNodes(whens.flatMap(_.conseq) ++ whens.flatMap(_.alt))
    }

    def findMemReads(stmts: Vector[lir.Stmt]): Vector[lir.MemRead] = {
      val reads = stmts.collect{ case r: lir.MemRead => r }
      val whens = stmts.collect{ case w: lir.When => w }

      reads ++ findMemReads(whens.flatMap(_.conseq) ++ whens.flatMap(_.alt))
    }

    val moduleStmts = module.components ++ module.inits ++ module.procedures

    val nodes = findNodes(moduleStmts)
    val commences = nodes.collect{ case lir.Node(_, commence: lir.Commence, _) => commence }
    val procs = commences.foldLeft(Vector.empty[lir.Commence]) { case (acc, commence) =>
      val sameProc = acc.map(_.path).contains(commence.path)
      val sameBlock = acc.map(_.origin).contains(commence.origin)

      if(sameProc && sameBlock) acc
      else acc :+ commence
    }

    val memReads = findMemReads(moduleStmts)
    val mems = memReads.foldLeft(Vector.empty[lir.MemRead]){
      case (acc, read) =>
        val sameMem = acc.map(_.name).contains(read.name)
        val samePort = acc.map(_.port).contains(read.port)

        if(sameMem && samePort) acc
        else acc :+ read
    }

    var idMax = id
    val procPointers = procs.map{ proc =>
      idMax += 1
      val hierarchy = HWHierarchyPath(modulePath, HierarchyComponent.Proc(proc.path.name.get, proc.origin))
      PointerConnection(idMax, hierarchy, Vector.empty, proc.tpe)
    }
    val memPointers = mems.map{ mem =>
      idMax += 1
      val hierarchy = HWHierarchyPath(modulePath, HierarchyComponent.Memory(mem.name, mem.port))
      PointerConnection(idMax, hierarchy, Vector.empty, mem.tpe)
    }

    val subPointers = Vector.newBuilder[PointerConnection]
    val nextID = module.subs.foldLeft(idMax){ case (id, sub) =>
      val module = moduleList.find(_.tpe == sub.tpe).get
      val subPath = modulePath :+ sub.name

      val (pointers, nextID) = searchSources(module, moduleList, subPath, id)
      subPointers ++= pointers
      nextID
    }

    val resultPointers = procPointers ++ memPointers ++ subPointers.result()
    (resultPointers, nextID)
  }

  private def searchDestinations(pointers: Vector[PointerConnection], topModule: lir.Module, moduleList: Vector[lir.Module]): Vector[PointerConnection] = {
    def searchFirstProcRef(path: HWHierarchyPath): Vector[lir.Reference] = {
      val module = searchModule(path.modulePath, topModule, moduleList)
      val HierarchyComponent.Proc(procName, blockName) = path.component
      val stmts = module.components ++ module.inits ++ module.procedures

      def loop(stmts: Vector[lir.Stmt]): Vector[lir.Reference] = {
        val whens = stmts.collect{ case when: lir.When => when }
        val whenStmts = whens.flatMap(w => w.conseq ++ w.alt)

        val commenceRefs = stmts.collect{ case node: lir.Node => node }
          .collect{ case lir.Node(name, c: lir.Commence, _) => (name, c) }
          .filter{ case (_, c) => c.path.name.get == procName }
          .filter{ case (_, c) => c.origin == blockName }
          .map{ case (name, c) => lir.Reference(name, c.tpe) }

        commenceRefs ++ loop(whenStmts)
      }

      loop(stmts)
    }

    def searchFirstMemRef(path: HWHierarchyPath): Vector[lir.Reference] = {
      val module = searchModule(path.modulePath, topModule, moduleList)
      val HierarchyComponent.Memory(memName, port) = path.component
      val stmts = module.components ++ module.inits ++ module.procedures

      def loop(stmts: Vector[lir.Stmt]): Vector[lir.Reference] = {
        val whens = stmts.collect{ case when: lir.When => when }
        val whenStmts = whens.flatMap(w => w.conseq ++ w.alt)
        val memRefs = stmts.collect{ case node: lir.Node => node }
          .collect{ case lir.Node(name, r: lir.Reference, _) => (name, r) }
          .filter{ case (_, r) => r.name == NameTemplate.memPointer(memName, port) }
          .map{ case (_, r) => r }

        memRefs ++ loop(whenStmts)
      }

      loop(stmts)
    }

    val procPointers = pointers.filter(_.source.component.isInstanceOf[HierarchyComponent.Proc]).map(p => (p, searchFirstProcRef(p.source)))
    val memPointers = pointers.filter(_.source.component.isInstanceOf[HierarchyComponent.Memory]).map(p => (p, searchFirstMemRef(p.source)))
    (procPointers ++ memPointers)
      .map { case (pointer, firstRefs) => pointer -> firstRefs.map(HierarchyComponent.Ref.apply) }
      .map { case (pointer, components) => pointer -> components.map(HWHierarchyPath(pointer.source.modulePath, _)) }
      .map { case (pointer, hierarchyPaths) =>
        val dsts = hierarchyPaths.flatMap(path => searchConnection(
          path,
          topModule,
          moduleList
        ))

      pointer.copy(dest = dsts)
    }
  }

  private def searchModule(modulePath: Vector[String], top: lir.Module, moduleList: Vector[lir.Module]): lir.Module = {
    @tailrec def loop(path: Vector[String], module: lir.Module): lir.Module = path match {
      case Vector() => module
      case path =>
        val sub = module.subs.find(_.name == path.head).get
        val mod = moduleList.find(_.tpe == sub.tpe).get

        loop(path.tail, mod)
    }

    loop(modulePath, top)
  }

  // ref   : reference of pointer as source
  // path  : module's path
  // module: current module
  //
  // return: deref pointer's path
  private def searchConnection(path: HWHierarchyPath, topModule: lir.Module, moduleList: Vector[lir.Module]): Vector[HWHierarchyPath] = {
    // In order to use these variable in inner method, defining here
    val module = searchModule(path.modulePath, topModule, moduleList)
    val componentRef = path.component.asInstanceOf[HierarchyComponent.Ref].ref

    // TODO: current implementation is not exhaustive verification
    //       For example,
    //         node a.expr <= pointer(...)
    //              ^^^^^^  <-\
    //         node t <= a     ---- these are checked
    //                   ^  <-/
    //       is acceptable pattern, actually.
    def searchPointerRef(refer: lir.Ref, origin: lir.Ref, modulePath: Vector[String]): Option[lir.Ref] = (refer, origin) match {
      case (refer: lir.Reference, origin: lir.Reference) =>
        if(refer.name != origin.name) None
        else Some(refer)
      case (refer: lir.Reference, origin: lir.SubField) =>
        searchPointerRef(refer, origin.prefix, modulePath).map {
          prefix => lir.SubField(prefix, origin.name, origin.tpe)
        }
      case (refer: lir.Reference, origin: lir.SubIndex) =>
        searchPointerRef(refer, origin.vec, modulePath).map {
          prefix => lir.SubIndex(prefix, origin.idx, origin.tpe)
        }
      case (refer: lir.Reference, origin: lir.SubAccess) =>
        searchPointerRef(refer, origin.vec, modulePath).map {
          prefix => lir.SubAccess(prefix, origin.idx, origin.tpe)
        }
      case (refer: lir.SubField, origin: lir.SubField) =>
        if(refer.name != origin.name) None
        else searchPointerRef(refer, origin, modulePath)
      case (_: lir.SubField, _) =>
        // other cases like
        //
        //  node a <=
        //       ^ origin           <-\
        //  node b <= a.hoge           ----- checked here
        //            ^^^^^^ refer  <-/
        //
        //  never happen when `a` is pointer, so return None
        None
      case (refer: lir.SubIndex, origin: lir.SubIndex) =>
        if(refer.idx != origin.idx) None
        else searchPointerRef(refer.vec, origin.vec, modulePath)
      case (refer: lir.SubIndex, origin: lir.SubAccess) =>
        searchPointerRef(refer.vec, origin.vec, modulePath).map {
          prefix => lir.SubIndex(prefix, refer.idx, refer.tpe)
        }
      case (_: lir.SubIndex, _) => None
      case (refer: lir.SubAccess, origin) => origin match {
        case lir.SubIndex(vec, _, _) => searchPointerRef(refer.vec, vec, modulePath).map(ref => lir.SubAccess(ref, refer.idx, refer.tpe))
        case lir.SubAccess(vec, _, _) => searchPointerRef(refer.vec, vec, modulePath).map(ref => lir.SubAccess(ref, refer.idx, refer.tpe))
        case _: lir.Reference => throw new ImplementationErrorException("refer[lib.SubAccess] from origin[lib.Reference] is not acceptable")
        case _: lir.SubField => throw new ImplementationErrorException("refer[lib.SubAccess] from origin[lib.SubField] is not acceptable")
      }
      case _ => None
    }

    def nextReference(dst: lir.Ref, src: lir.Ref, pointer: lir.Ref, modulePath: Vector[String]): HWHierarchyPath = {
      def addHead(subject: lir.Ref, head: lir.Reference): lir.Ref = subject match {
        case lir.Reference(name, tpe) => lir.SubField(head, name, tpe)
        case sub @ lir.SubField(prefix, _, _) => sub.copy(prefix = addHead(prefix, head))
        case sub @ lir.SubIndex(prefix, _, _) => sub.copy(vec = addHead(prefix, head))
        case sub @ lir.SubAccess(prefix, _, _) => sub.copy(vec = addHead(prefix, head))
      }

      def truncateHead(subject: lir.Ref, head: lir.Ref): lir.Ref = {
        subject match {
          case sub @ lir.SubField(ref: lir.SubField, name, tpe) =>
            if(sameRef(ref, head)) lir.Reference(name, tpe)
            else sub.copy(prefix = truncateHead(ref, head))
          case _ => throw new ImplementationErrorException("truncate from lir.Ref except lir.SubField is unacceptable")
        }
      }

      // a <= b.c.d
      // pointer is `b.c.d.e.f`
      // as a result `a.e.f` is new pointer
      //
      // a.b <= c.d.e
      // pointer is `c.d.e.f.g`
      // as a result, `a.b.f.g` is new pointer
      //
      // a.b.c <= d.e.f
      // pointer is `d.e.f`
      // as a result, `a.b.c` is new pointer
      def changeHeads(subject: lir.Ref, dst: lir.Ref, src: lir.Ref): lir.Ref = subject match {
        case _: lir.Reference => dst
        case sub @ lir.SubField(prefix, _, _) =>
          if(sameRef(subject, src)) dst
          else sub.copy(prefix = changeHeads(prefix, dst, src))
        case sub @ lir.SubIndex(prefix, _, _) =>
          if(sameRef(subject, src)) dst
          else sub.copy(vec = changeHeads(prefix, dst, src))
        case sub @ lir.SubAccess(prefix, _, _) =>
          if(sameRef(subject, src)) dst
          else sub.copy(vec = changeHeads(prefix, dst, src))
      }

      @tailrec def getHead(ref: lir.Ref): lir.Reference = ref match {
        case ref: lir.Reference         => ref
        case lir.SubField(prefix, _, _) => getHead(prefix)
        case lir.SubIndex(vec, _, _)    => getHead(vec)
        case lir.SubAccess(vec, _, _)   => getHead(vec)
      }

      @tailrec def sameRef(a: lir.Ref, b: lir.Ref): Boolean = (a, b) match {
        case (lir.Reference(n0, _), lir.Reference(n1, _)) => n0 == n1
        case (lir.SubField(p0, n0, _), lir.SubField(p1, n1, _)) => n0 == n1 && sameRef(p0, p1)
        case (lir.SubIndex(p0, i0, _), lir.SubIndex(p1, i1, _)) => i0 == i1 && sameRef(p0, p1)
        case (lir.SubAccess(p0, _, _), lir.SubAccess(p1, _, _)) => sameRef(p0, p1)
        case _ => false
      }

      // this nextRef is temporary
      // because reference of head can be submodule's name
      // In that case, nextRef's head is truncated and Add head into modulePath's last position
      val nextRef = changeHeads(pointer, dst, src)
      val lir.Reference(name, _) = getHead(nextRef)
      val thisModuleRef = lir.Reference(modulePath.last, searchModule(modulePath, topModule, moduleList).tpe)
      val portOpt = module.ports
        .find(_.name == name)
        .map(_ => (modulePath.init, addHead(nextRef, thisModuleRef)))
      val subOpt = module.subs
        .find(_.name == name)
        .map(sub => (modulePath :+ sub.name, truncateHead(nextRef, thisModuleRef)))

      val (nextModulePath, nextReference) = (portOpt, subOpt) match {
        case (Some(next), _) => next
        case (_, Some(next)) => next
        case (_, _) => (modulePath, nextRef)
      }

      HWHierarchyPath(nextModulePath, HierarchyComponent.Ref(nextReference))
    }

    def searchNext(stmt: lir.Stmt): Vector[HWHierarchyPath] = stmt match {
      case lir.Reg(name, Some(default), tpe)  =>
        searchPointerRef(default, componentRef, path.modulePath)
          .map{ pointer => nextReference(
            lir.Reference(name, tpe),
            default,
            pointer,
            path.modulePath
          )}
          .toVector
      case t: lir.Assign =>
        searchPointerRef(t.src, componentRef, path.modulePath)
          .map { pointer => nextReference(
            t.dst,
            t.src,
            pointer,
            path.modulePath
          )}
          .toVector
      case t: lir.When =>
        t.conseq.flatMap(searchNext) ++ t.alt.flatMap(searchNext)
      case t: lir.Node =>
        t.src match {
          case src: lir.Ref =>
            searchPointerRef(src, componentRef, path.modulePath)
              .map{ pointer => nextReference(
                lir.Reference(t.name, t.tpe),
                src,
                pointer,
                path.modulePath
              )}
              .toVector
          case _ => Vector.empty
        }
      case _ => Vector.empty
    }

    def searchDeref(stmt: lir.Stmt): Vector[HWHierarchyPath] = stmt match {
      case t: lir.Node => t.src match {
        case lir.Deref(ref, _) =>
          searchPointerRef(ref, componentRef, path.modulePath)
            .map(_ => HWHierarchyPath(path.modulePath, HierarchyComponent.Deref(ref)))
            .toVector
        case _ => Vector.empty
      }
      case t: lir.When => t.conseq.flatMap(searchDeref) ++ t.alt.flatMap(searchDeref)
    }

    val stmts = module.components ++ module.inits ++ module.procedures
    val nextRefs = stmts.flatMap(searchNext)
    val derefs = stmts.flatMap(searchDeref)

    val dsts = nextRefs.flatMap(path => searchConnection(path, topModule, moduleList))
    derefs ++ dsts
  }
}

trait HierarchyComponent
object HierarchyComponent {
  case class Memory(name: String, port: Int) extends HierarchyComponent
  case class Proc(name: String, origin: String) extends HierarchyComponent
  case class Ref(ref: lir.Ref) extends HierarchyComponent
  case class Deref(ref: lir.Reference) extends HierarchyComponent
}

case class HWHierarchyPath(modulePath: Vector[String], component: HierarchyComponent) {
  def toFirrtlString = ("Top" +: modulePath).mkString("_")
  def add(name: String): HWHierarchyPath = this.copy(modulePath = this.modulePath :+ name)
  override def hashCode() = modulePath.hashCode()
}
case class PointerConnection(
  id: Int,
  source: HWHierarchyPath,
  dest: Vector[HWHierarchyPath],
  tpe: BackendType
)

