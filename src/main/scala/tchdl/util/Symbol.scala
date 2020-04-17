package tchdl.util

import tchdl.ast.Expression

abstract class Symbol(ctx: Context, __tpe: Type) {
  val name: String
  val namespace: NameSpace = ctx.namespace
  val fullPath: NameSpace = namespace.append(name)

  private var isAlreadyReferenced = false
  private var _tpe: Type = __tpe
  def setTpe(tpe: Type): Unit = _tpe = tpe
  def tpe: Type = {
    val isReferenced = isAlreadyReferenced
    isAlreadyReferenced = true

    _tpe match {
      case _: Type.TypeGenerator if isReferenced =>
        ???
      case gen: Type.TypeGenerator =>
        val tpe = gen.generate()
        _tpe = tpe
        tpe
      case tpe => tpe
    }
  }

  private var _flag: Modifier = Modifier.NoModifier
  def setFlag(flag: Modifier): this.type = { _flag = flag; this }
  def addFlag(flag: Modifier): this.type = { _flag |= flag; this }
  def hasFlag(flag: Modifier): Boolean = { _flag.hasFlag(flag) }
  def flag: Modifier = _flag

  override def equals(obj: Any): Boolean = symEq(obj)
  protected def symEq(obj: Any): Boolean

  def asTypeSymbol: Symbol.TypeSymbol = this.asInstanceOf[Symbol.TypeSymbol]
  def asTermSymbol: Symbol.TermSymbol = this.asInstanceOf[Symbol.TermSymbol]
}

object Symbol {
  class TypeSymbol(val name: String, tpe: Type, ctx: Context) extends Symbol(ctx, tpe) {
    override def symEq(obj: Any): Boolean = obj match {
      case obj: TypeSymbol => this.fullPath == obj.fullPath
      case _ => false
    }

    def makeRefType(tp: Vector[Expression]): Either[Error, Type.RefType] = tpe match {
      case tpe: Type.DeclaredType =>
        def lengthCheck: Either[Error, Unit] = {
          val paramLength = tpe.hardwareParam.length + tpe.typeParam.length
          if(paramLength != tp.length)

        }



    }
  }

  object TypeSymbol {
    def apply(name: String, tpe: Type, ctx: Context): TypeSymbol =
      new TypeSymbol(name, tpe, ctx)
  }

  class TermSymbol(val name: String, tpe: Type, ctx: Context) extends Symbol(ctx, tpe) {
    override def symEq(obj: Any): Boolean = obj match {
      case obj: TermSymbol => this.fullPath == obj.fullPath
      case _ => false
    }
  }

  object TermSymbol {
    def apply(name: String, tpe: Type, ctx: Context): TermSymbol =
      new TermSymbol(name, tpe, ctx)
  }
}

