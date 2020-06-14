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

