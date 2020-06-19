package tchdl.typecheck

import tchdl.ast._
import tchdl.util.TchdlException.ImplementationErrorException
import tchdl.util._

import scala.annotation.tailrec

object ImplMethodSigTyper {
  def exec(cu: CompilationUnit)(implicit global: GlobalData): Unit = {
    val ctx = getContext(cu.pkgName, cu.filename.get)

    cu.topDefs.collect{
      case impl: ImplementClass => verifyImplClass(impl)(ctx, global)
      case impl: ImplementInterface => verifyImplInterface(impl)(ctx, global)
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

    val (valErrs, _) = impl.components
      .collect { case v: ValDef => v }
      .map{ verifyValDef(_)(implCtx, global) }
      .partitionMap(identity)

    val errs = methodErrs ++ stageErrs ++ valErrs
    errs.foreach(global.repo.error.append)
  }

  def verifyImplInterface(impl: ImplementInterface)(implicit ctx: Context.RootContext, global: GlobalData): Unit = {
    def verifyMethodSignatureValidity(implMethod: Symbol.MethodSymbol)(implicit ctx: Context.NodeContext): Either[Error, Unit] = {
      def lookupInterfaceMethod(interface: Symbol.InterfaceSymbol, name: String): Either[Error, Symbol.MethodSymbol] =
        interface.tpe
          .asEntityType
          .declares
          .lookup(name)
          .map(symbol => Right(symbol.asMethodSymbol))
          .getOrElse(Left(Error.ImplementMethodInterfaceNotHas(implMethod, interface)))

      def verifyModifier(implMethod: Symbol.MethodSymbol, interfaceMethod: Symbol.MethodSymbol): Either[Error, Unit] = {
        if(implMethod.flag == interfaceMethod.flag) Right(())
        else Left(Error.ModifierMismatch(interfaceMethod.flag, implMethod.flag))
      }

      def verifySignatureLength(implMethod: Symbol.MethodSymbol, interfaceMethod: Symbol.MethodSymbol): Either[Error, Unit] = {
        def verify(expect: Int, actual: Int, err: (Int, Int) => Error): Either[Error, Unit] =
          if(expect == actual) Right(())
          else Left(err(expect, actual))

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

      def verifyHPValidity(
        implHPBounds: Vector[HPBound],
        interfaceHPBounds: Vector[HPBound]
      ): Either[Error, Unit] = {
        def verifyBounds(impls: Vector[HPBound], interfaces: Vector[HPBound]): Either[Error, Unit] =
          (impls zip interfaces)
            .map{ case (impl, interface) => verifyBound(impl, interface) }
            .combine(errs => Error.MultipleErrors(errs: _*))

        def verifyBound(impl: HPBound, interface: HPBound): Either[Error, Unit] = {
          @tailrec def verifyExprs(exprs0: Vector[HPExpr], exprs1: Vector[HPExpr]): Either[Error, Unit] = {
            exprs1.headOption match {
              case None if exprs0.nonEmpty => Left(Error.NotEnoughHPBound(interface))
              case None => Right(())
              case Some(expr1) => exprs0.findRemain(_.isSameExpr(expr1)) match {
                case (None, _) => Left(Error.NotEnoughHPBound(interface))
                case (Some(_), remains) => verifyExprs(remains, exprs1.tail)
              }
            }
          }

          def verifyConstRange(c0: HPRange.ConstantRange, c1: HPRange.ConstantRange): Either[Error, Unit] = {
            val isValid =
              c0.max == c1.max &&
              c0.min == c1.min &&
              c0.ne == c1.ne

            if (isValid) Right(())
            else Left(Error.NotEnoughHPBound(interface))
          }

          (impl.bound, interface.bound) match {
            case (HPRange.Eq(HPRange.ConstantEqual(v0)), HPRange.Eq(HPRange.ConstantEqual(v1))) =>
              if (v0 == v1) Right(())
              else Left(Error.NotEnoughHPBound(interface))
            case (HPRange.Eq(HPRange.ExprEqual(e0)), HPRange.Eq(HPRange.ExprEqual(e1))) =>
              if (e0.isSameExpr(e1)) Right(())
              else Left(Error.NotEnoughHPBound(interface))
            case (HPRange.Range(e0, c0), HPRange.Range(e1, c1)) =>
              for {
                _ <- verifyExprs(e0.max, e1.max)
                _ <- verifyExprs(e0.min, e1.min)
                _ <- verifyExprs(e0.ne, e1.ne)
                _ <- verifyConstRange(c0, c1)
              } yield ()
          }
        }

        def buildPairs(implBounds: Vector[HPBound], interfaceBounds: Vector[HPBound]): Either[Error, Vector[(HPBound, HPBound)]] =
          interfaceBounds.headOption match {
            case None if implBounds.nonEmpty => Left(Error.ExcessiveHPBound(implBounds))
            case None => Right(Vector.empty)
            case Some(interface) => implBounds.findRemain(_.target.isSameExpr(interface.target)) match {
              case (None, _) => Left(Error.NotEnoughHPBound(interface))
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
            case None if impls.nonEmpty => Left(Error.ExcessiveTPBound(impls))
            case None => Right(Vector.empty)
            case Some(interface) => impls.findRemain(_.target =:= interface.target) match {
              case (None, _) => Left(Error.NotEnoughTPBound(interface))
              case (Some(impl), remains) => buildPairs(remains, interfaces.tail).map((impl, interface) +: _)
            }
          }
        }

        def verifyBounds(impls: Vector[TPBound], interfaces: Vector[TPBound]): Either[Error, Unit] = {
          (impls zip interfaces)
            .map{ case (impl, interface) => verifyBound(impl, interface) }
            .combine(errs => Error.MultipleErrors(errs: _*))
        }

        def verifyBound(impl: TPBound, interface: TPBound): Either[Error, Unit] = {
          @tailrec def loop(implBounds: Vector[Type.RefType], interfaceBounds: Vector[Type.RefType]): Either[Error, Unit] = {
            interfaceBounds.headOption match {
              case None if implBounds.nonEmpty => Left(Error.ExcessiveTPBound(Vector(impl)))
              case None => Right(())
              case Some(interfaceBound) => implBounds.findRemain(_ == interfaceBound) match {
                case (None, _) => Left(Error.NotEnoughTPBound(interface))
                case (Some(_), remains) => loop(remains, interfaceBounds.tail)
              }
            }
          }

          loop(impl.bounds, interface.bounds)
        }

        for {
          pairs <- buildPairs(implTPBound, interfaceTPBound)
          (impls, interfaces) = pairs.unzip
          _ <- verifyBounds(impls, interfaces)
        } yield ()
      }

      def compareMethodSignature(
        implMethod: Type.MethodType,
        interfaceMethod: Type.MethodType
      ): Either[Error, Unit] = {
        val implTpes = implMethod.params :+ implMethod.returnType
        val interfaceTpes = interfaceMethod.params :+ interfaceMethod.returnType
        val results = (implTpes zip interfaceTpes).map {
          case (impl, interface) if impl =:= interface => Right(())
          case (impl, interface) => Left(Error.TypeMismatch(interface, impl))
        }

        results.combine(errs => Error.MultipleErrors(errs: _*))
      }

      val interfaceTpe = impl.interface.tpe.asRefType
      val interfaceSymbol = interfaceTpe.origin.asInterfaceSymbol

      for {
        interfaceMethod <- lookupInterfaceMethod(interfaceSymbol, implMethod.name)
        _ <- verifyModifier(implMethod, interfaceMethod)
        _ <- verifySignatureLength(implMethod, interfaceMethod)
        hpIdents = implMethod.hps.map(hp => Ident(hp.name).setSymbol(hp).setTpe(hp.tpe))
        methodHPTable = (interfaceMethod.hps zip hpIdents).toMap
        interfaceHPTable = (interfaceSymbol.hps zip interfaceTpe.hardwareParam).toMap
        hpTable = methodHPTable ++ interfaceHPTable
        replacedHPBounds = HPBound.swapBounds(interfaceMethod.hpBound, hpTable)
        _ <- verifyHPValidity(implMethod.hpBound, replacedHPBounds)
        tpRefs = implMethod.tps.map(Type.RefType.apply)
        methodTPTable = (interfaceMethod.tps zip tpRefs).toMap
        interfaceTPTable = (interfaceSymbol.tps zip interfaceTpe.typeParam).toMap
        tpTable = methodTPTable ++ interfaceTPTable
        replacedTPBounds = TPBound.swapBounds(interfaceMethod.tpBound, hpTable, tpTable)
        _ <- verifyTPValidity(implMethod.tpBound, replacedTPBounds)
        replacedMethodTpe = interfaceMethod.tpe.asMethodType.replaceWithMap(hpTable, tpTable)
        _ <- compareMethodSignature(implMethod.tpe.asMethodType, replacedMethodTpe)
      } yield ()
    }

    val implSigCtx = Context(ctx, impl.symbol)
    val implSymbol = impl.symbol.asImplementSymbol

    implSigCtx.reAppend(
      implSymbol.hps ++
      implSymbol.tps: _*
    )

    val implCtx = Context(implSigCtx, impl.target.tpe.asRefType)
    impl.methods.foreach(_.symbol.tpe)

    val (errs, methodSymbols) = impl.methods.map(verifyMethodDef(_)(implCtx, global)).partitionMap(identity)
    val result =
      if(errs.nonEmpty) Left(Error.MultipleErrors(errs: _*))
      else {
        methodSymbols
          .map(verifyMethodSignatureValidity(_)(implCtx))
          .combine(errs => Error.MultipleErrors(errs: _*))
      }

    result.left.foreach(global.repo.error.append)

    // search methods that is not implemented at impl's context
    val interfaceMethods = impl.interface.symbol
      .tpe.asEntityType
      .declares
      .toMap.collect{ case (name, method: Symbol.MethodSymbol) => name -> method }

    interfaceMethods.map{
      case (name, _) if impl.methods.exists(_.name == name) => Right(())
      case (_, method) => Left(Error.RequireImplementMethod(method))
    }
      .toVector
      .combine(errs => Error.MultipleErrors(errs: _*))
      .left
      .foreach(global.repo.error.append)
  }

  def verifyMethodDef(methodDef: MethodDef)(implicit ctx: Context.NodeContext, global: GlobalData): Either[Error, Symbol.MethodSymbol] = {
    def verifyModifierValidity: Either[Error, Unit] = {
      val self = ctx.self.getOrElse(throw new ImplementationErrorException("This type should be there"))
      val validModifiers = self.origin match {
        case _: Symbol.StructSymbol => Vector(Modifier.NoModifier)
        case _: Symbol.ModuleSymbol => Vector(
          Modifier.Input | Modifier.Sibling,
          Modifier.Input,
          Modifier.Sibling,
          Modifier.Parent,
          Modifier.NoModifier
        )
      }

      if(validModifiers.contains(methodDef.flag)) Right(())
      else Left(Error.InvalidModifier(validModifiers, methodDef.flag))
    }

    def verifyMethodTpe: Either[Error, Unit] = {
      val modMethodModifier = Vector (
        Modifier.Input | Modifier.Sibling,
        Modifier.Input,
        Modifier.Sibling,
        Modifier.Parent,
      )

      val isInterfaceMethod = modMethodModifier.contains(methodDef.flag)
      val paramTpes = methodDef.params.map(_.symbol.tpe)
      val retTpe = methodDef.retTpe.tpe

      val paramResults = paramTpes.map {
        case Type.ErrorType => Left(Error.DummyError)
        case tpe: Type.RefType if isInterfaceMethod && tpe.isHardwareType => Right(())
        case tpe: Type.RefType if isInterfaceMethod => Left(Error.RequireHardwareType(tpe))
        case _ => Right(())
      }

      val retResult = retTpe match {
        case Type.ErrorType => Left(Error.DummyError)
        case tpe: Type.RefType if tpe =:= Type.unitTpe => Right(())
        case tpe: Type.RefType if isInterfaceMethod && tpe.isHardwareType => Right(())
        case tpe: Type.RefType if isInterfaceMethod => Left(Error.RequireHardwareType(tpe))
        case _ => Right(())
      }

      (paramResults :+ retResult).combine(errs => Error.MultipleErrors(errs: _*))
    }

    methodDef.symbol.tpe
    val methodSymbol = methodDef.symbol.asMethodSymbol
    val signatureCtx = Context(ctx, methodSymbol)
    signatureCtx.reAppend (methodSymbol.hps ++ methodSymbol.tps: _*)

    for {
      _ <- TyperUtil.verifyTPBoundType(methodSymbol)(signatureCtx, global)
      _ <- verifyModifierValidity
      _ <- verifyMethodTpe
    } yield methodSymbol
  }

  def verifyStageDef(stageDef: StageDef)(implicit ctx: Context.NodeContext, global: GlobalData): Either[Error, Symbol.StageSymbol] = {
    def verifyDefinitionPositionValidity(self: Type.RefType, stage: Symbol.StageSymbol): Either[Error, Type.MethodType]  = self.origin match {
      case _: Symbol.StructSymbol => Left(Error.ImplementModuleComponentInStruct(self))
      case _: Symbol.ModuleSymbol => stage.tpe match {
        case Type.ErrorType => Left(Error.DummyError)
        case tpe: Type.MethodType => Right(tpe)
      }
    }

    def verifySignature(stage: Type.MethodType): Either[Error, Unit] = {
      val errs = stage.params.filterNot(_.isHardwareType).map(Error.RequireHardwareType.apply).map(Left.apply[Error, Unit])
      val err =
        if(stage.returnType =:= Type.unitTpe) Right(())
        else Left(Error.RequireSpecificType(stage.returnType, Type.unitTpe))

      (errs :+ err).combine(errs => Error.MultipleErrors(errs: _*))
    }

    stageDef.symbol.tpe
    val stageSymbol = stageDef.symbol.asStageSymbol
    val self = ctx.self.getOrElse(throw new ImplementationErrorException("this type should be there"))

    for {
      stageTpe <- verifyDefinitionPositionValidity(self, stageSymbol)
      _ <- verifySignature(stageTpe)
    } yield stageSymbol
  }

  def verifyValDef(vdef: ValDef)(implicit ctx: Context.NodeContext, globla: GlobalData): Either[Error, Symbol.VariableSymbol] = {
    val self = ctx.self.getOrElse(throw new ImplementationErrorException("this type should be there"))
    self.origin match {
      case _: Symbol.StructSymbol => Left(Error.ImplementModuleComponentInStruct(self))
      case _: Symbol.ModuleSymbol => vdef.tpeTree match {
        case None => Left(Error.RequireTypeTree)
        case Some(_) => vdef.symbol.tpe match {
          case Type.ErrorType => Left(Error.DummyError)
          case _: Type.RefType => Right(vdef.symbol.asVariableSymbol)
        }
      }
    }
  }
}
