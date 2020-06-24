package tchdl.backend

import tchdl.ast._
import tchdl.util._
import tchdl.util.TchdlException.ImplementationErrorException
import tchdl.typecheck.Typer

object BuildGeneratedModuleList {
  def exec(implicit global: GlobalData): Option[Vector[BuiltModule]] = {
    def getPackage: Either[Error, Symbol.PackageSymbol] =
      global.rootPackage.search(global.command.topModulePkg)

    def buildTypeTree(moduleTree: TypeTree, pkg: Symbol.PackageSymbol): Either[Error, TypeTree] = {
      val rootCtx = pkg.context.values.head
      val dummySymbol = Symbol.StructSymbol("dummy", pkg.path.appendName("dummy"), Accessibility.Private, Modifier.NoModifier, Type.NoType)
      val nodeCtx = new Context.NodeContext(rootCtx, dummySymbol, None, None)
      val moduleTypeTree = Typer.typedTypeTree(moduleTree)(nodeCtx, global)

      if(global.repo.error.elems.isEmpty) Right(moduleTypeTree)
      else Left(Error.DummyError)
    }

    def verifyType(tpe: Type.RefType): Either[Error, Unit] = {
      def verifyHPExpr(expr: HPExpr): Either[Error, Unit] = expr match {
        case _: IntLiteral => Right(())
        case _: StringLiteral => Right(())
        case expr => Left(Error.RequireLiteral(expr))
      }

      (tpe.hardwareParam.map(verifyHPExpr) ++ tpe.typeParam.map(verifyType))
        .combine(errs => Error.MultipleErrors(errs: _*))
    }

    val topModuleTree = global.command.topModule.get

    val list = for {
      pkg <- getPackage
      typeTree <- buildTypeTree(topModuleTree, pkg)
      topModuleTpe = typeTree.tpe.asRefType
      _ <- verifyType(topModuleTpe)
      moduleList <- constructModule(topModuleTpe, Vector.empty, Vector.empty)
    } yield (moduleList, topModuleTpe)

    list match {
      case Left(err) =>
        global.repo.error.append(err)
        None
      case Right((moduleList, topModuleTpe)) =>
        global.topModule = Some(topModuleTpe)
        Some(moduleList)
    }
  }

  def constructModule(module: Type.RefType, parentModules: Vector[Type.RefType], builtModules: Vector[BuiltModule])(implicit global: GlobalData): Either[Error, Vector[BuiltModule]] = {
    def verifyCyclic: Either[Error, Unit] = {
      if(parentModules.drop(1).forall(_ =!= module)) Right(())
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

    def buildChildren(impl: ImplementClassContainer): Either[Error, (Vector[Int], Vector[BuiltModule])] = {
      val implTree = searchTree[ImplementClass](impl.id).getOrElse(throw new ImplementationErrorException("implementation tree must be found"))
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
      val subModuleResult = subModuleTpes.foldLeft[Either[Error, (Vector[Int], Vector[BuiltModule])]](Right(Vector.empty, builtModules)){
        case (Right((ids, built)), module) if built.forall(_.module =!= module) =>
          constructModule(module, module +: parentModules, built)
            .map(builtList => (ids :+ builtList.head.id, builtList))
        case (Right((ids, built)), module) =>
          val submod = built.find(_.module =:= module)
            .getOrElse(throw new ImplementationErrorException("module that is already built should be found"))

          Right(ids :+ submod.id, built)
        case (Left(err), _) => Left(err)
      }

      subModuleResult match {
        case Left(err) => Left(err)
        case Right(pair) => Right(pair)
      }
    }

    verifyCyclic match {
      case Left(err) => Left(err)
      case Right(_) =>
        val impl = findImplementClass
        impl.map(buildChildren) match {
          case None => Right(BuiltModule(module, None, Vector.empty) +: builtModules)
          case Some(Left(err)) => Left(err)
          case Some(Right((childIDs, modules))) => Right(BuiltModule(module, impl, childIDs) +: modules)
        }
    }
  }
}
