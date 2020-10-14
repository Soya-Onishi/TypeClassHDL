package tchdl.typecheck

import tchdl.ast._
import tchdl.util.TchdlException.ImplementationErrorException
import tchdl.util._

import scala.annotation.tailrec

object ImplMethodSigTyper {
  def exec(cu: CompilationUnit)(implicit global: GlobalData): Unit = {
    val ctx = getContext(cu.pkgName, cu.filename)

    cu.topDefs.collect {
      case impl: ImplementClass => verifyImplClass(impl)(ctx, global)
      case impl: ImplementInterface => verifyImplInterface(impl)(ctx, global)
      case method: MethodDef => verifyMethodDef(method)(ctx, global)
    }
  }

  def verifyImplClass(impl: ImplementClass)(implicit ctx: Context.RootContext, global: GlobalData): Unit = {
    val implSigCtx = Context(ctx, impl.symbol)
    val implSymbol = impl.symbol.asImplementSymbol

    implSigCtx.reAppend(
      implSymbol.hps ++
        implSymbol.tps: _*
    )

    val implCtx = Context(implSigCtx, impl.target.tpe.asRefType)

    val (methodErrs, _) = impl.components
      .collect { case m: MethodDef => m }
      .map(verifyMethodDef(_)(implCtx, global))
      .partitionMap(identity)

    val (stageErrs, _) = impl.components
      .collect { case s: StageDef => s }
      .map(verifyStageDef(_)(implCtx, global))
      .partitionMap(identity)

    val (procErrs, _) = impl.components
      .collect{ case p: ProcDef => p }
      .map(verifyProcDef(_)(implCtx, global))
      .partitionMap(identity)

    val (valErrs, _) = impl.components
      .collect { case v: ValDef => v }
      .map { verifyValDef(_)(implCtx, global) }
      .partitionMap(identity)

    val errs = methodErrs ++ stageErrs ++ procErrs ++ valErrs
    errs.foreach(global.repo.error.append)
  }

  def verifyImplInterface(impl: ImplementInterface)(implicit ctx: Context.RootContext, global: GlobalData): Unit = {
    def verifyMethodSignatureValidity(implMethod: Symbol.MethodSymbol, fieldTypes: Map[String, Symbol.FieldTypeSymbol])(implicit ctx: Context.NodeContext): Either[Error, Unit] = {
      def lookupInterfaceMethod(interface: Symbol.InterfaceSymbol, name: String): Either[Error, Symbol.MethodSymbol] =
        interface.tpe
          .asEntityType
          .declares
          .lookup(name)
          .map(symbol => Right(symbol.asMethodSymbol))
          .getOrElse(Left(Error.ImplementMethodInterfaceNotHas(implMethod, interface, impl.position)))

      def verifyModifier(implMethod: Symbol.MethodSymbol, interfaceMethod: Symbol.MethodSymbol): Either[Error, Unit] = {
        if (implMethod.flag == interfaceMethod.flag) Right(())
        else Left(Error.ModifierMismatch(interfaceMethod.flag, implMethod.flag, impl.position))
      }

      def verifySignatureLength(implMethod: Symbol.MethodSymbol, interfaceMethod: Symbol.MethodSymbol): Either[Error, Unit] = {
        def verify(expect: Int, actual: Int, err: (Int, Int, Position) => Error): Either[Error, Unit] =
          if (expect == actual) Right(())
          else Left(err(expect, actual, impl.position))

        val results = Vector(
          verify(interfaceMethod.hps.length, implMethod.hps.length, Error.HardParameterLengthMismatch.apply),
          verify(interfaceMethod.tps.length, implMethod.tps.length, Error.TypeParameterLengthMismatch.apply),
          verify(
            interfaceMethod.tpe.asMethodType.params.length,
            implMethod.tpe.asMethodType.params.length,
            Error.ParameterLengthMismatch.apply
          )
        )

        results.combine(errs => Error.MultipleErrors(errs: _*))
      }

      def verifyHPValidity(implHPBounds: Vector[HPBound], interfaceHPBounds: Vector[HPBound]
                          ): Either[Error, Unit] = {
        def verifyBounds(impls: Vector[HPBound], interfaces: Vector[HPBound]): Either[Error, Unit] =
          (impls zip interfaces)
            .filter { case (impl, interface) => impl.bound != interface.bound }
            .map { case (implBound, interface) => Error.HPBoundConstraintMismatch(implBound.bound, interface.bound, impl.position) }
            .combine(errs => Error.MultipleErrors(errs: _*))

        def buildPairs(implBounds: Vector[HPBound], interfaceBounds: Vector[HPBound]): Either[Error, Vector[(HPBound, HPBound)]] =
          interfaceBounds.headOption match {
            case None if implBounds.nonEmpty => Left(Error.ExcessiveHPBound(implBounds, impl.position))
            case None => Right(Vector.empty)
            case Some(interface) => implBounds.findRemain(_.target.isSameExpr(interface.target)) match {
              case (None, _) => Left(Error.NotEnoughHPBound(interface, impl.position))
              case (Some(impl), remains) => buildPairs(remains, interfaceBounds.tail).map((impl, interface) +: _)
            }
          }

        for {
          pairs <- buildPairs(implHPBounds, interfaceHPBounds)
          (impls, interfaces) = pairs.unzip
          _ <- verifyBounds(impls, interfaces)
        } yield ()
      }

      def verifyTPValidity(
        implTPBound: Vector[TPBound],
        interfaceTPBound: Vector[TPBound]
      ): Either[Error, Unit] = {
        def buildPairs(impls: Vector[TPBound], interfaces: Vector[TPBound]): Either[Error, Vector[(TPBound, TPBound)]] = {
          interfaces.headOption match {
            case None if impls.nonEmpty => Left(Error.ExcessiveTPBound(impls, impl.position))
            case None => Right(Vector.empty)
            case Some(interface) => impls.findRemain(_.target =:= interface.target) match {
              case (None, _) => Left(Error.NotEnoughTPBound(interface, impl.position))
              case (Some(impl), remains) => buildPairs(remains, interfaces.tail).map((impl, interface) +: _)
            }
          }
        }

        def verifyBounds(impls: Vector[TPBound], interfaces: Vector[TPBound]): Either[Error, Unit] = {
          (impls zip interfaces)
            .map { case (impl, interface) => verifyBound(impl, interface) }
            .combine(errs => Error.MultipleErrors(errs: _*))
        }

        def verifyBound(implBound: TPBound, interface: TPBound): Either[Error, Unit] = {
          @tailrec def loop(implBounds: Vector[Type.RefType], interfaceBounds: Vector[Type.RefType]): Either[Error, Unit] = {
            interfaceBounds.headOption match {
              case None if implBounds.nonEmpty => Left(Error.ExcessiveTPBound(Vector(implBound), impl.position))
              case None => Right(())
              case Some(interfaceBound) => implBounds.findRemain(_ == interfaceBound) match {
                case (None, _) => Left(Error.NotEnoughTPBound(interface, impl.position))
                case (Some(_), remains) => loop(remains, interfaceBounds.tail)
              }
            }
          }

          loop(implBound.bounds, interface.bounds)
        }

        for {
          pairs <- buildPairs(implTPBound, interfaceTPBound)
          (impls, interfaces) = pairs.unzip
          _ <- verifyBounds(impls, interfaces)
        } yield ()
      }

      def replaceThisType(interfaceType: Type.RefType, implThisType: Type.RefType): Type.RefType = {
        if (interfaceType.origin.isInterfaceSymbol) implThisType
        else interfaceType
      }

      def compareMethodSignature(
        implMethod: Type.MethodType,
        interfaceMethod: Type.MethodType,
        implFieldTypes: Map[String, Symbol.FieldTypeSymbol]
      ): Either[Error, Unit] = {
        val implThisType = ctx.self.getOrElse(throw new ImplementationErrorException("impl should have self type"))

        val implTpes = implMethod.params :+ implMethod.returnType
        val interfaceTpes = (interfaceMethod.params :+ interfaceMethod.returnType).map(replaceThisType(_, implThisType))
        val results = (implTpes zip interfaceTpes).map {
          case (impl, interface) if impl == interface => Right(())
          case (implTpe, interface) => interface.origin match {
            case symbol: Symbol.FieldTypeSymbol if implFieldTypes(symbol.name).tpe == implTpe => Right(())
            case _ => Left(Error.TypeMismatch(interface, implTpe, impl.position))
          }
        }

        results.combine(errs => Error.MultipleErrors(errs: _*))
      }

      val interfaceTpe = impl.interface.tpe.asRefType
      val interfaceSymbol = interfaceTpe.origin.asInterfaceSymbol

      for {
        interfaceMethod <- lookupInterfaceMethod(interfaceSymbol, implMethod.name)
        _ <- verifyModifier(implMethod, interfaceMethod)
        _ <- verifySignatureLength(implMethod, interfaceMethod)
        hpIdents = implMethod.hps.map(hp => Ident(hp.name, Position.empty).setSymbol(hp).setTpe(hp.tpe))
        methodHPTable = (interfaceMethod.hps zip hpIdents).toMap
        interfaceHPTable = (interfaceSymbol.hps zip interfaceTpe.hardwareParam).toMap
        hpTable = methodHPTable ++ interfaceHPTable
        replacedHPBounds = HPBound.swapBounds(interfaceMethod.hpBound, hpTable)
        _ <- verifyHPValidity(implMethod.hpBound, replacedHPBounds)
        tpRefs = implMethod.tps.map(Type.RefType.apply(_, isPointer = false))
        methodTPTable = (interfaceMethod.tps zip tpRefs).toMap
        interfaceTPTable = (interfaceSymbol.tps zip interfaceTpe.typeParam).toMap
        tpTable = methodTPTable ++ interfaceTPTable
        replacedTPBounds = TPBound.swapBounds(interfaceMethod.tpBound, hpTable, tpTable)
        _ <- verifyTPValidity(implMethod.tpBound, replacedTPBounds)
        replacedMethodTpe = interfaceMethod.tpe.asMethodType.replaceWithMap(hpTable, tpTable)
        _ <- compareMethodSignature(implMethod.tpe.asMethodType, replacedMethodTpe, fieldTypes)
      } yield ()
    }

    val implSigCtx = Context(ctx, impl.symbol)
    val implSymbol = impl.symbol.asImplementSymbol

    implSigCtx.reAppend(
      implSymbol.hps ++
      implSymbol.tps: _*
    )

    val implCtx = Context(implSigCtx, impl.target.tpe.asRefType)
    val fieldTypes = impl.types.map(tpe => tpe.name -> tpe.symbol.asFieldTypeSymbol).toMap

    impl.methods.foreach(_.symbol.tpe)

    val (errs, methodSymbols) = impl.methods.map(verifyMethodDef(_)(implCtx, global)).partitionMap(identity)
    val result =
      if (errs.nonEmpty) Left(Error.MultipleErrors(errs: _*))
      else {
        methodSymbols
          .map(verifyMethodSignatureValidity(_, fieldTypes)(implCtx))
          .combine(errs => Error.MultipleErrors(errs: _*))
      }

    result.left.foreach(global.repo.error.append)

    // search methods that is not implemented at impl's context
    val interfaceDeclares = impl.interface.symbol.tpe.asEntityType.declares
    val interfaceMethods = interfaceDeclares.toMap.collect {
      case (name, method: Symbol.MethodSymbol) => name -> method
    }
    val interfaceTypes = interfaceDeclares.toMap.collect {
      case (name, tpeSymbol: Symbol.FieldTypeSymbol) => name -> tpeSymbol
    }

    val methodResults = interfaceMethods.toVector.map {
      case (name, _) if impl.methods.exists(_.name == name) => Right(())
      case (_, method) => Left(Error.RequireImplementMethod(method, impl.position))
    }

    val typeResults = interfaceTypes.toVector.map {
      case (name, _) if impl.types.exists(_.name == name) => Right(())
      case (_, tpe) => Left(Error.RequireImplementType(tpe, impl.position))
    }

    (methodResults ++ typeResults)
      .combine(errs => Error.MultipleErrors(errs: _*))
      .left
      .foreach(global.repo.error.append)
  }

  def verifyMethodDef(methodDef: MethodDef)(implicit ctx: Context, global: GlobalData): Either[Error, Symbol.MethodSymbol] = {
    def verifyModifierValidity: Either[Error, Unit] = {
      val validModifiers = ctx.self match {
        case None => Vector(Modifier.NoModifier)
        case Some(tpe) => tpe.origin match {
          case _: Symbol.StructSymbol => Vector(Modifier.NoModifier, Modifier.Static)
          case _: Symbol.ModuleSymbol =>
            Vector(
              Modifier.Input | Modifier.Sibling,
              Modifier.Input,
              Modifier.Sibling,
              Modifier.Parent,
              Modifier.Internal,
              Modifier.Static,
              Modifier.NoModifier
            )
        }
      }

      if (validModifiers.contains(methodDef.flag)) Right(())
      else Left(Error.InvalidModifier(validModifiers, methodDef.flag, methodDef.position))
    }

    def verifyMethodTpe: Either[Error, Unit] = {
      def isValidForSig(tpe: Type.RefType, pos: Position): Boolean = {
        val isHW = tpe.isHardwareType(ctx.tpBounds)(pos, global)

        isHW || tpe.isPointer
      }

      val moduleInterfaceModifier = Vector(
        Modifier.Input | Modifier.Sibling,
        Modifier.Input,
        Modifier.Sibling,
        Modifier.Parent,
      )

      val isInterfaceMethod = moduleInterfaceModifier.contains(methodDef.flag)
      val paramTpes = methodDef.params.map(_.symbol.tpe)
      val retTpe = methodDef.retTpe.tpe

      val paramResults = (paramTpes zip methodDef.params).map {
        case (Type.ErrorType, _) => Left(Error.DummyError)
        case (tpe: Type.RefType, param) if isInterfaceMethod && isValidForSig(tpe, param.position) => Right(())
        case (tpe: Type.RefType, param) if isInterfaceMethod => Left(Error.RequirePointerOrHWType(tpe, param.position))
        case _ => Right(())
      }

      val retResult = retTpe match {
        case Type.ErrorType => Left(Error.DummyError)
        case tpe: Type.RefType if tpe =:= Type.unitTpe => Right(())
        case tpe: Type.RefType if isInterfaceMethod && isValidForSig(tpe, methodDef.retTpe.position) => Right(())
        case tpe: Type.RefType if isInterfaceMethod => Left(Error.RequirePointerOrHWType(tpe, methodDef.retTpe.position))
        case _ => Right(())
      }

      (paramResults :+ retResult).combine(errs => Error.MultipleErrors(errs: _*))
    }

    methodDef.symbol.tpe match {
      case Type.ErrorType => methodDef.retTpe.setTpe(Type.ErrorType)
      case Type.MethodType(_, ret) => methodDef.retTpe.setTpe(ret)
    }

    val methodSymbol = methodDef.symbol.asMethodSymbol
    val signatureCtx = Context(ctx, methodSymbol)
    signatureCtx.reAppend(methodSymbol.hps ++ methodSymbol.tps: _*)

    for {
      _ <- TyperUtil.verifyHPBoundType(methodSymbol)(global)
      _ <- TyperUtil.verifyTPBoundType(methodSymbol)(signatureCtx, global)
      _ <- verifyModifierValidity
      _ <- verifyMethodTpe
    } yield methodSymbol
  }

  def verifyStageDef(stageDef: StageDef)(implicit ctx: Context.NodeContext, global: GlobalData): Either[Error, Symbol.StageSymbol] = {
    def verifyDefinitionPositionValidity(self: Type.RefType, stage: Symbol.StageSymbol): Either[Error, Type.MethodType] = self.origin match {
      case _: Symbol.StructSymbol => Left(Error.ImplementModuleComponentInStruct(self, stageDef.position))
      case _: Symbol.ModuleSymbol => stage.tpe match {
        case Type.ErrorType => Left(Error.DummyError)
        case tpe: Type.MethodType => Right(tpe)
      }
    }

    def isValidForParam(tpe: Type.RefType, pos: Position): Boolean = {
      val isHW = tpe.isHardwareType(ctx.tpBounds)(pos, global)
      isHW || tpe.isPointer
    }


    def verifySignature(stage: Type.MethodType): Either[Error, Unit] = {
      val errs = (stage.params zip stageDef.params)
        .filterNot{ case (tpe, param) => isValidForParam(tpe, param.position) }
        .map{ case (tpe, param) => Error.RequirePointerOrHWType(tpe, param.position) }
        .map(Left.apply[Error, Unit])

      errs.combine(errs => Error.MultipleErrors(errs: _*))
    }

    stageDef.symbol.tpe
    val stageSymbol = stageDef.symbol.asStageSymbol
    val self = ctx.self.getOrElse(throw new ImplementationErrorException("this type should be there"))

    for {
      stageTpe <- verifyDefinitionPositionValidity(self, stageSymbol)
      _ <- verifySignature(stageTpe)
    } yield stageSymbol
  }

  def verifyProcDef(pdef: ProcDef)(implicit ctx: Context.NodeContext, global: GlobalData): Either[Error, Symbol.ProcSymbol] = {
    pdef.symbol.tpe match {
      case Type.ErrorType => Left(Error.DummyError)
      case procTpe: Type.MethodType =>
        val retTpe = procTpe.returnType

        if(retTpe.isPointer) Right(pdef.symbol.asProcSymbol)
        else Left(Error.RequirePointerTypeAsProcRet(retTpe, pdef.retTpe.position))
      case tpe => throw new ImplementationErrorException(s"Expect MethodType for proc symbol but actual: ${tpe.getClass}")
    }
  }

  def verifyValDef(vdef: ValDef)(implicit ctx: Context.NodeContext, global: GlobalData): Either[Error, Symbol.VariableSymbol] = {
    val self = ctx.self.getOrElse(throw new ImplementationErrorException("this type should be there"))
    self.origin match {
      case _: Symbol.StructSymbol => Left(Error.ImplementModuleComponentInStruct(self, vdef.position))
      case _: Symbol.ModuleSymbol => vdef.tpeTree match {
        case None => Left(Error.RequireTypeTree(vdef.position))
        case Some(_) => vdef.symbol.tpe match {
          case Type.ErrorType => Left(Error.DummyError)
          case _: Type.RefType => Right(vdef.symbol.asVariableSymbol)
        }
      }
    }
  }
}
