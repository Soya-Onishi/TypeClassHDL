package tchdl.backend

import tchdl.ast._
import tchdl.util._
import tchdl.util.TchdlException.ImplementationErrorException
import tchdl.typecheck.Typer

object BuildGeneratedModuleList {
  def exec(implicit global: GlobalData): Vector[BuiltModule] = {
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
      refTpe = typeTree.tpe.asRefType
      _ <- verifyType(refTpe)
      topModuleTpe = convertToBackendType(refTpe, Map.empty, Map.empty)
      moduleList <- constructModule(topModuleTpe, Vector.empty, Vector.empty)
    } yield moduleList

    list.left.foreach(global.repo.error.append)
    list.getOrElse(Vector.empty)
  }

  def constructModule(module: BackendType, parentModules: Vector[BackendType], builtModules: Vector[BuiltModule])(implicit global: GlobalData): Either[Error, Vector[BuiltModule]] = {
    def verifyCyclic: Either[Error, Unit] = {
      if(parentModules.drop(1).forall(_ == module)) Right(())
      else {
        def buildRoute(parents: Vector[BackendType]): Vector[BackendType] =
          parents.headOption match {
            case None => Vector.empty
            case Some(tpe) if tpe == module => Vector.empty
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

    def findImplementClass: Option[ImplementClassContainer] = {
      val refTpe = convertToRefType(module)
      module.symbol.asModuleSymbol.impls.find {
        impl =>
          val (initHPTable, initTPTable) = Type.RefType.buildTable(impl)
          val result = for {
            hpTable <- Type.RefType.assignHPTable(initHPTable, Vector(refTpe), Vector(impl.targetType))
            tpTable <- Type.RefType.assignTPTable(initTPTable, Vector(refTpe), Vector(impl.targetType))
            swappedHPBound = HPBound.swapBounds(impl.symbol.hpBound, hpTable)
            swappedTPBound = TPBound.swapBounds(impl.symbol.tpBound, hpTable, tpTable)
            simplifiedHPBound <- HPBound.simplify(swappedHPBound)
            _ <- verifyEachBounds(simplifiedHPBound, swappedTPBound)
          } yield ()

          result.isRight
      }
    }

    def buildChildren(impl: ImplementClassContainer, parent: BackendType): Either[Error, Vector[BuiltModule]] = {
      val implTree = findImplClassTree(impl.symbol.asImplementSymbol, global).getOrElse(throw new ImplementationErrorException("implementation tree must be found"))
      val subModules = implTree.components.collect {
        case vdef: ValDef if vdef.flag.hasFlag(Modifier.Child) => vdef
      }

      val hpTable = buildHPTable(impl.symbol.hps, parent, impl.targetType)
      val tpTable = buildTPTable(impl.symbol.tps, parent, impl.targetType)

      val subModuleTpes = subModules.view
        .map(_.symbol.tpe.asRefType)
        .map(convertToBackendType(_, hpTable, tpTable))
        .to(Vector)

      val result = subModuleTpes.foldLeft[Either[Error, Vector[BuiltModule]]](Right(builtModules)) {
        case (Right(modules), subModule) if modules.exists(_.module == subModule)  => Right(modules)
        case (Right(modules), subModule) => constructModule(subModule, subModule +: parentModules, modules)
        case (Left(err), _) => Left(err)
      }

      result match {
        case Left(err) => Left(err)
        case Right(builtModules) =>
          val built = BuiltModule(parent, Some(impl), subModuleTpes)
          Right(built +: builtModules)
      }
    }

    verifyCyclic match {
      case Left(err) => Left(err)
      case Right(_) =>
        val impl = findImplementClass
        impl.map(buildChildren(_, module)) match {
          case None => Right(BuiltModule(module, None, Vector.empty) +: builtModules)
          case Some(Left(err)) => Left(err)
          case Some(Right(modules)) => Right(modules)
        }
    }
  }
}
