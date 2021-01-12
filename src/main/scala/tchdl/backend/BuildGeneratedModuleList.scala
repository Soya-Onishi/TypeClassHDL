package tchdl.backend

import tchdl.ast._
import tchdl.util._
import tchdl.util.TchdlException.ImplementationErrorException
import tchdl.typecheck.Typer

object BuildGeneratedModuleList {
  def exec(implicit global: GlobalData): Vector[BuiltModule] = {
    def getPackage: Either[Error, Symbol.PackageSymbol] =
      global.rootPackage.search(global.config.topModulePkg)

    def buildTypeTree(moduleTree: TypeTree, pkg: Symbol.PackageSymbol): Either[Error, TypeTree] = {
      val rootCtx = pkg.context.values.head
      val dummySymbol = Symbol.StructSymbol("dummy", pkg.path, Accessibility.Private, Modifier.NoModifier, Type.NoType)
      val nodeCtx = new Context.NodeContext(rootCtx, dummySymbol, None, dummySymbol.path, isStatic = false)
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

    val topModuleTree = global.config.topModule.get

    val elaboratedModuleList = for {
      pkg <- getPackage
      typeTree <- buildTypeTree(topModuleTree, pkg)
      refTpe = typeTree.tpe.asRefType
      _ <- verifyType(refTpe)
      topModuleTpe = toBackendType(refTpe, Map.empty, Map.empty)
      elaboratedModuleList <- constructModule(topModuleTpe, Vector.empty, Vector.empty)
    } yield elaboratedModuleList ++ getIndirectFromTopModule(refTpe, topModuleTpe)

    elaboratedModuleList.left.foreach(global.repo.error.append)
    elaboratedModuleList.getOrElse(Vector.empty)
  }

  def findImplementClasses(module: BackendType)(implicit global: GlobalData): Vector[ImplementClassContainer] = {
    def verifyEachBounds(hpBounds: Vector[HPBound], tpBounds: Vector[TPBound]): Either[Error, Unit] = {
      val hpResults = hpBounds.map(bound => HPBound.verifyMeetBound(bound, Vector.empty))
      val tpResults = tpBounds.map(bound => TPBound.verifyMeetBound(bound, Vector.empty, Vector.empty, Position.empty))
      (hpResults ++ tpResults).combine(errs => Error.MultipleErrors(errs: _*))
    }

    val refTpe = toRefType(module)
    module.symbol.asModuleSymbol.impls.filter {
      impl =>
        val (initHPTable, initTPTable) = Type.RefType.buildTable(impl)
        val result = for {
          hpTable <- Type.RefType.assignHPTable(initHPTable, Vector(refTpe), Vector(impl.targetType), impl.position)
          tpTable <- Type.RefType.assignTPTable(initTPTable, Vector(refTpe), Vector(impl.targetType), impl.position)
          swappedHPBound = HPBound.swapBounds(impl.symbol.hpBound, hpTable)
          swappedTPBound = TPBound.swapBounds(impl.symbol.tpBound, hpTable, tpTable)
          simplifiedHPBound = HPBound.simplify(swappedHPBound)
          _ <- verifyEachBounds(simplifiedHPBound, swappedTPBound)
        } yield ()

        result.isRight
    }
  }

  def constructModule(module: BackendType, parentModules: Vector[BackendType], builtModules: Vector[BuiltModule])(implicit global: GlobalData): Either[Error, Vector[BuiltModule]] = {
    def verifyCyclic: Either[Error, Unit] = {
      if(!parentModules.drop(1).contains(module)) Right(())
      else {
        def buildRoute(parents: Vector[BackendType]): Vector[BackendType] =
          parents.headOption match {
            case None => Vector.empty
            case Some(tpe) if tpe == module => Vector.empty
            case Some(tpe) => tpe +: buildRoute(parents.tail)
          }

        val route = buildRoute(parentModules)

        Left(Error.CyclicModuleInstantiation(module, route, Position.empty))
      }
    }

    def buildChildren(impl: ImplementClassContainer, parent: BackendType): Either[Error, Vector[BuiltModule]] = {
      val implTree = findImplClassTree(impl.symbol.asImplementSymbol, global).getOrElse(throw new ImplementationErrorException("implementation tree must be found"))
      val subModules = implTree.components
        .collect { case vdef: ValDef => vdef }
        .filter (_.flag.hasFlag(Modifier.Child))
        .filter (_.symbol != Symbol.mem)

      val hpTable = buildHPTable(impl.symbol.hps, parent, impl.targetType)
      val tpTable = buildTPTable(impl.symbol.tps, parent, impl.targetType)

      val subModuleTpes = subModules.view
        .map(_.symbol.tpe.asRefType)
        .map(toBackendType(_, hpTable, tpTable))
        .toVector

      subModuleTpes.foldLeft[Either[Error, Vector[BuiltModule]]](Right(builtModules)) {
        case (Right(modules), subModule) if modules.map(_.tpe).toSet.contains(subModule)  => Right(modules)
        case (Right(modules), subModule) => constructModule(subModule, subModule +: parentModules, modules)
        case (Left(err), _) => Left(err)
      }
    }

    verifyCyclic match {
      case Left(err) => Left(err)
      case Right(_) =>
        val thisModuleImpls = findImplementClasses(module)
        val (errs, builtModuless) = thisModuleImpls.map(buildChildren(_, module)).partitionMap(identity)

        if(errs.nonEmpty) Left(Error.MultipleErrors(errs: _*))
        else {
          val appendedModules = builtModuless.foldLeft[Vector[BuiltModule]](builtModules) {
            case (acc, modules) =>
              val assigns = modules.filterNot(module => acc.exists(_.tpe == module.tpe))
              acc ++ assigns
          }

          val thisModule = BuiltModule(module, thisModuleImpls, noNeedElaborate = false)
          Right(thisModule +: appendedModules)
        }
    }
  }

  def getIndirectFromTopModule(tpe: Type.RefType, tpeBack: BackendType)(implicit global: GlobalData): Vector[BuiltModule] = {
    val topHPs = (tpe.origin.hps zip tpeBack.hargs).toMap
    val topTPs = (tpe.origin.tps zip tpeBack.targs).toMap

    tpe.declares
      .toMap.values
      .map(_.tpe.asRefType)
      .map(tpe => toBackendType(tpe, topHPs, topTPs))
      .map(tpe => BuiltModule(tpe, findImplementClasses(tpe), noNeedElaborate = true))
      .toVector
  }
}
