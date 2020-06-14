package tchdl

import tchdl.util._
import tchdl.util.TchdlException._

package object typecheck {
  def getContext(pkgName: Vector[String], filename: String)(implicit global: GlobalData): Context.RootContext =
    global.rootPackage.search(pkgName)
      .getOrElse(throw new ImplementationErrorException(s"[${pkgName.mkString("::")}] should be there"))
      .lookupCtx(filename)
      .getOrElse(throw new ImplementationErrorException(s"[$filename]'s context should be there'"))
}
