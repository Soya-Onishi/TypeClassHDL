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

    def collectPartition[B](f: PartialFunction[A, B]): (Vector[B], Vector[A]) = {
      f.unapply(vec.head) match {
        case Some(elem) => vec.tail match {
          case Vector() => (Vector(elem), Vector.empty)
          case tail =>
            val (bs, as) = tail.collectPartition(f)
            (elem +: bs, as)
        }
        case None => vec.tail match {
          case Vector() => (Vector.empty, Vector(vec.head))
          case tail =>
            val (bs, as) = tail.collectPartition(f)
            (bs, vec.head +: as)
        }
      }
    }
  }
}
