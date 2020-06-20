package tchdl.backend

import tchdl.ast._
import tchdl.util._
import tchdl.util.TchdlException.ImplementationErrorException

object ConstructStructure {
  def constructModule(module: Type.RefType, parentModules: Vector[Type.RefType])(implicit global: GlobalData): Either[Error, StructureNode] = {
    def verifyCyclic: Either[Error, Unit] = {
      if(parentModules.forall(_ =!= module)) Right(())
      else {
        def buildRoute(parents: Vector[Type.RefType]): Vector[Type.RefType] =
          parents.headOption match {
            case None => Vector.empty
            case Some(tpe) if tpe =:= module => Vector.empty
            case Some(tpe) => tpe +: buildRoute(parents.tail)
          }

        val route = buildRoute(parentModules)

        Left(Error.CyclicModuleInstantiation(module, route))
      }
    }

    def verifyEachBounds(hpBounds: Vector[HPBound], tpBounds: Vector[TPBound]): Either[Error, Unit] = {
      val hpResults = hpBounds.map(bound => HPBound.verifyMeetBound(bound, Vector.empty))
      val tpResults = tpBounds.map(bound => TPBound.verifyMeetBound(bound, Vector.empty, Vector.empty))
      (hpResults ++ tpResults).combine(errs => Error.MultipleErrors(errs: _*))
    }

    def findImplementClass: Option[ImplementClassContainer] =
      module.origin.asModuleSymbol.impls.find {
        impl =>
          val (initHPTable, initTPTable) = Type.RefType.buildTable(impl)
          val result = for {
            hpTable <- Type.RefType.assignHPTable(initHPTable, Vector(module), Vector(impl.targetType))
            tpTable <- Type.RefType.assignTPTable(initTPTable, Vector(module), Vector(impl.targetType))
            swappedHPBound = HPBound.swapBounds(impl.symbol.hpBound, hpTable)
            swappedTPBound = TPBound.swapBounds(impl.symbol.tpBound, hpTable, tpTable)
            simplifiedHPBound <- HPBound.simplify(swappedHPBound)
            _ <- verifyEachBounds(simplifiedHPBound, swappedTPBound)
          } yield ()

          result.isRight
      }

    def buildChildren(impl: ImplementClassContainer): Either[Error, Vector[StructureNode]] = {
      val implTree = searchTree[ImplementClass](impl.symbol)
      val subModules = implTree.components.collect {
        case vdef: ValDef if vdef.flag.hasFlag(Modifier.Child) => vdef
      }
      val (initHPTable, initTPTable) = Type.RefType.buildTable(impl)
      val constructedTable = for {
        hpTable <- Type.RefType.assignHPTable(initHPTable, Vector(module), Vector(impl.targetType))
        tpTable <- Type.RefType.assignTPTable(initTPTable, Vector(module), Vector(impl.targetType))
      } yield (hpTable, tpTable)
      val (hpTable, tpTable) = constructedTable
        .getOrElse(
          throw new ImplementationErrorException("Failed to build hardware parameter and type parameter table")
        )

      val subModuleTpes = subModules.map(_.symbol.tpe.asRefType.replaceWithMap(hpTable, tpTable))
      val (errs, nodes) = subModuleTpes.map(constructModule(_, module +: parentModules)).partitionMap(identity)

      if(errs.nonEmpty) Left(Error.MultipleErrors(errs: _*))
      else Right(nodes)
    }

    verifyCyclic match {
      case Left(err) => Left(err)
      case Right(_) =>
        val impl = findImplementClass
        impl.map(buildChildren) match {
          case None => Right(StructureNode(module, None, Vector.empty))
          case Some(Left(err)) => Left(err)
          case Some(Right(nodes)) => Right(StructureNode(module, impl, nodes))
        }
    }
  }
}
