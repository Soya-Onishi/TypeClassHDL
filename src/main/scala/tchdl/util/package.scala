package tchdl

package object util {
  implicit class VectorFindElement[A](vec: Vector[A]) {
    def collectFirstRemain[B](f: PartialFunction[A, B]): (Option[B], Vector[A]) = {
      f.unapply(vec.head) match {
        case elem@Some(_) => (elem, vec.tail)
        case None => vec.tail match {
          case Vector() => (None, Vector.empty)
          case tail =>
            val (found, remain) = tail.collectFirstRemain(f)
            (found, vec.head +: remain)
        }
      }
    }

    def collectPartition[B](f: PartialFunction[A, B]): (Vector[B], Vector[A]) = vec match {
      case Vector() => (Vector.empty, Vector.empty)
      case elems => f.unapply(elems.head) match {
          case Some(elem) =>
            val (bs, as) = elems.tail.collectPartition(f)
            (elem +: bs, as)
          case None =>
            val (bs, as) = elems.tail.collectPartition(f)
            (bs, elems.head +: as)
      }
    }

    def findRemain(f: A => Boolean): (Option[A], Vector[A]) = vec match {
      case Vector() => (Option.empty, Vector.empty)
      case elems if f(elems.head) => (Some(elems.head), elems.tail)
      case elems =>
        val (opt, tail) = elems.tail.findRemain(f)
        (opt, elems.head +: tail)
    }
  }

  implicit class VectorEitherUnit[A](vec: Vector[Either[A, Unit]]) {
    def combine[B](f: Vector[A] => B): Either[B, Unit] = {
      val (lefts, _) = vec.partitionMap(identity)

      if(lefts.isEmpty) Right(())
      else Left(f(lefts))
    }
  }
}
