package tchdl.typecheck

import tchdl.ast._
import tchdl.util.TchdlException.ImplementationErrorException
import tchdl.util._

import scala.annotation.tailrec
import scala.reflect.{ClassTag, classTag}
import scala.reflect.runtime.universe.{TypeTag, typeTag}

// TODO:
//   Add logic to verify whether all type parameters are used at signature
//   e.g. impl[A, B] Interface[A] for Type[B] is valid.
//        However, impl[A, B] Interface[A] for Type is invalid(B is not used).
object VerifyImplConflict {
  def verifyImplConflict()(implicit global: GlobalData): Unit = {
    /*
    def verifySameForm(
      tpe0: Type.RefType,
      tpe1: Type.RefType,
      hpBound0: Vector[HPBound],
      hpBound1: Vector[HPBound],
      tpBound0: Vector[TPBound],
      tpBound1: Vector[TPBound]
    ): Option[Type.RefType] = {
      tpe0.isOverlapped(tpe1, hpBound0, hpBound1, tpBound0, tpBound1)

      (tpe0.origin, tpe1.origin) match {
        case (_: Symbol.TypeParamSymbol, _: Symbol.TypeParamSymbol) => Some(tpe0)
        case (_: Symbol.EntityTypeSymbol, _: Symbol.EntityTypeSymbol) =>
          val tps = tpe0.typeParam
            .zip(tpe1.typeParam)
            .map{ case (t0, t1) => verifySameForm(t0, t1) }

          if(tps.exists(_.isEmpty)) None
          else Some(Type.RefType(tpe0.origin, tpe0.hardwareParam, tps.flatten))
        case (_: Symbol.EntityTypeSymbol, _: Symbol.TypeParamSymbol) if tpe0 <|= tpe1 => Some(tpe0)
        case (_: Symbol.TypeParamSymbol, _: Symbol.EntityTypeSymbol) if tpe1 <|= tpe0 => Some(tpe1)
        case (_, _) => None
      }
    }
     */

    /**
     * This function insert RefType that has entity type origin into
     * RefType that has type parameter origin.
     *
     * E.g.
     *    impl0: impl[A1, B1] Interface[ST[A1]] for Type[B1]
     *    impl1: impl[A2, B2] Interface[A2] for Type[ST[B2]]
     *                        ↓
     *    impl0: impl[A1]     Interface[ST[A1]] for Type[ST[B2]]
     *    impl1: impl[A2, B2] Interface[A2]     for Type[ST[B2]]
     *
     *    map will have one pair (B1 -> ST[B2]) in this case
     * param impl0 impl that has types which are replaced from type parameter into entity type
     * param impl1 impl that has types which are used to replace impl0's type parameter
     * param map   table of (type parameters -> entity type)
     * param tpes  this function used to get all types impl has
     * tparam T    ImplementContainer
     */
    /*
  def insertRefType[T <: ImplementContainer](
    impl0: T,
    impl1: T,
    map: mutable.Map[Symbol.TypeParamSymbol, Option[Type.RefType]]
  )(
    tpes: T => Vector[Type.RefType]
  ): Unit = {
    def inner(tpe0: Type.RefType, tpe1: Type.RefType): Vector[(Symbol.TypeParamSymbol, Type.RefType)] = {
      (tpe0.origin, tpe1.origin) match {
        case (t: Symbol.TypeParamSymbol, _) if tpe1 <|= tpe0 => Vector(t -> tpe1)
        case (t0: Symbol.EntityTypeSymbol, t1: Symbol.EntityTypeSymbol) if t0 == t1 =>
          tpe0.typeParam
            .zip(tpe1.typeParam)
            .flatMap{ case (t0, t1) => inner(t0, t1) }
        case (_, _) => Vector.empty
      }
    }

    val tab = map.collect { case (key, Some(value)) => key -> value }.toMap
    val vec = tpes(impl0)
      .zip(tpes(impl1))
      .map{ case (tpe0, tpe1) => (tpe0.replaceWithMap(tab), tpe1.replaceWithMap(tab)) }
      .flatMap{ case (tpe0, tpe1) => inner(tpe0, tpe1) }

    vec.groupBy(_._1)
      .map{ case (key, pairs) => key -> pairs.head._2 }
      .foreach{ case (key, value) => map(key) = Some(value) }
  }
   */

    @tailrec
    def verifyClassImplConflict(impls: Vector[ImplementClassContainer]): Unit = {
      def verify(impl0: ImplementClassContainer, impl1: ImplementClassContainer): Either[Error, Unit] = {
        val hasConflict = ImplementClassContainer.isConflict(impl0, impl1)

        if(hasConflict) Left(Error.ImplementClassConflict(impl0, impl1))
        else Right(())
      }

      if(impls.tail.nonEmpty) {
        impls.tail
          .map(verify(impls.head, _))
          .collect{ case Left(err) => err }
          .foreach(global.repo.error.append)

        verifyClassImplConflict(impls.tail)
      }
    }

    @tailrec
    def verifyInterfaceImplConflict(impls: Vector[ImplementInterfaceContainer]): Unit = {
      def verify(impl0: ImplementInterfaceContainer, impl1: ImplementInterfaceContainer): Either[Error, Unit] = {
        val isConflict = ImplementInterfaceContainer.isConflict(impl0, impl1)

        if(isConflict) Left(Error.ImplementInterfaceConflict(impl0, impl1))
        else Right(())
      }

      if(impls.tail.nonEmpty) {
        impls.tail
          .map(verify(impls.head, _))
          .collect{ case Left(err) => err }
          .foreach(global.repo.error.append)

        verifyInterfaceImplConflict(impls.tail)
      }
    }

    global.buffer.interface.symbols.foreach(interface => verifyInterfaceImplConflict(interface.impls))
    global.buffer.clazz.symbols.foreach(tpe => verifyClassImplConflict(tpe.impls))
  }
}

