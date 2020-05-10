package tchdl.util

object TchdlException {
  class ImplementationErrorException(msg: String) extends Exception(msg)
}
