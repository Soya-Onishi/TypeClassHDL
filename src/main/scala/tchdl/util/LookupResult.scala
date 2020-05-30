package tchdl.util

trait LookupResult[+T] {
  def map[B](f: T => B): LookupResult[B] = this match {
    case LookupResult.LookupSuccess(symbol) => LookupResult.LookupSuccess(f(symbol))
    case failure: LookupResult.LookupFailure[_] => failure.asInstanceOf[LookupResult[B]]
  }

  def flatMap[B](f: T => LookupResult[B]): LookupResult[B] = this match {
    case LookupResult.LookupSuccess(symbol) => f(symbol)
    case failure: LookupResult.LookupFailure[_] => failure.asInstanceOf[LookupResult[B]]
  }

  def foreach(f: T => Unit): Unit = this match {
    case LookupResult.LookupSuccess(symbol) => f(symbol)
    case _ =>
  }

  def toEither: Either[Error, T] = this match {
    case LookupResult.LookupSuccess(symbol) => Right(symbol)
    case LookupResult.LookupFailure(err) => Left(err)
  }

  def toOption: Option[T] = this match {
    case LookupResult.LookupSuccess(symbol) => Some(symbol)
    case LookupResult.LookupFailure(_) => None
  }
}

object LookupResult {
  case class LookupSuccess[T](symbol: T) extends LookupResult[T]
  case class LookupFailure[T](err: Error) extends LookupResult[T]
}