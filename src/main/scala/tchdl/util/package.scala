package tchdl

import scala.collection.generic.{CanBuildFrom, MapFactory}
import scala.util.Try

package object util {
  type HPTable = Map[Symbol.HardwareParamSymbol, tchdl.ast.HPExpr]
  type TPTable = Map[Symbol.TypeParamSymbol, Type.RefType]

  implicit class TraversableEitherUnit[A, F[+X] <: Traversable[X]](iter: F[Either[A, Unit]]) {
    def combine[B](f: F[A] => B)(implicit cbf: CanBuildFrom[F[A], A, F[A]]): Either[B, Unit] = {
      val builder = cbf()

      iter.foreach {
        case Left(elem) => builder += elem
        case Right(_) =>
      }

      val lefts = builder.result()
      if(lefts.isEmpty) Right(())
      else Left(f(lefts))
    }
  }

  implicit class TraversableUtil[T, F[X] <: Traversable[X]](iter: F[T]) {
    def partitionMap[A1, A2](f: T => Either[A1, A2])(implicit cbfa1: CanBuildFrom[F[T], A1, F[A1]], cbfa2: CanBuildFrom[F[T], A2, F[A2]]): (F[A1], F[A2]) = {
      val builderA1 = cbfa1()
      val builderA2 = cbfa2()

      iter.foreach { f(_) match {
        case Left(a1) =>  builderA1 += a1
        case Right(a2) =>  builderA2 += a2
      }}

      (builderA1.result(), builderA2.result())
    }

    def collectFirstRemain[B](f: PartialFunction[T, B])(implicit cbfa: CanBuildFrom[F[T], T, F[T]]): (Option[B], F[T]) = {
      var firstElem = Option.empty[B]
      val builder = cbfa()

      iter.foreach {
        case elem if firstElem.isEmpty && f.isDefinedAt(elem) => firstElem = Some(f(elem))
        case elem => builder += elem
      }

      (firstElem, builder.result())
    }

    def collectPartition[B](f: PartialFunction[T, B])(implicit cbfb: CanBuildFrom[F[T], B, F[B]], cbf: CanBuildFrom[F[T], T, F[T]]): (F[B], F[T]) = {
      val builderB = cbfb()
      val builderT = cbf()

      iter.foreach {
        case elem if f.isDefinedAt(elem) => builderB += f(elem)
        case elem => builderT += elem
      }

      (builderB.result(), builderT.result())
    }

    def findRemain(f: T => Boolean)(implicit cbf: CanBuildFrom[F[T], T, F[T]]): (Option[T], F[T]) = {
      var foundElem = Option.empty[T]
      val builder = cbf()

      iter.foreach {
        case elem if foundElem.isEmpty && f(elem) => foundElem = Some(elem)
        case elem => builder += elem
      }

      (foundElem, builder.result())
    }

    def combine[B](f: F[T] => B): Either[B, Unit] = {
      if(iter.isEmpty) Right(())
      else Left(f(iter))
    }
  }

  implicit class Unzip4Traversable[A, B, C, D, F[T] <: Traversable[T]](iter: F[(A, B, C, D)]) {
    type T = (A, B, C, D)

    def unzip4(implicit cbfa: CanBuildFrom[F[T], A, F[A]], cbfb: CanBuildFrom[F[T], B, F[B]], cbfc: CanBuildFrom[F[T], C, F[C]], cbfd: CanBuildFrom[F[T], D, F[D]]): (F[A], F[B], F[C], F[D]) = {
      val builderA = cbfa()
      val builderB = cbfb()
      val builderC = cbfc()
      val builderD = cbfd()

      iter.foreach {
        case (a, b, c, d) =>
          builderA += a
          builderB += b
          builderC += c
          builderD += d
      }

      (builderA.result, builderB.result, builderC.result, builderD.result)
    }
  }

  implicit class MapFactoryUtil[CC[X, Y] <: Map[X, Y] with scala.collection.MapLike[X, Y, CC[X, Y]], A, B](factory: MapFactory[CC]) {
    def from(iter: Seq[(A, B)]): CC[A, B] = {
      factory(iter: _*)
    }
  }

  implicit class ToXXXOption(from: String) {
    def toIntOption: Option[Int] = Try(from.toInt).toOption
  }
}
