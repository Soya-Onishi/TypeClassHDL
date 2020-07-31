package tchdl

import scala.reflect.macros.whitebox
import scala.language.experimental.macros
import scala.annotation.StaticAnnotation
import scala.annotation.compileTimeOnly

@compileTimeOnly("enable macro paradise to expand macro annotations")
class ASTree extends StaticAnnotation {
  def macroTransform(annottees: Any*): Any = macro CloneASTMacro.impl
}

object CloneASTMacro {
  def impl(c: whitebox.Context)(annottees: c.Expr[Any]*): c.Expr[Any] = {
    import c.universe._

    val (cdef: ClassDef) :: _ = annottees.map(_.tree).toList

    val apply = makeApplyMethod(c)(cdef)
    val copy = makeCopyMethod(c)(cdef)

    val companion =
      q"""
         object ${TermName(cdef.name.toString)} {
           $apply
         }
       """

    val caseClassParams = cdef.impl.body
      .collect{ case d: DefDef => d }
      .find(_.name == termNames.CONSTRUCTOR)
      .get
      .vparamss


    val caseClass =
      q"""
         case class ${cdef.name}(...$caseClassParams) extends ..${cdef.impl.parents} {
           $copy
         }
       """

    c.Expr[Any](
      q"""{
        $companion
        $caseClass
        }"""
    )
  }

  def makeApplyMethod(c: whitebox.Context)(clazz: c.universe.ClassDef): c.Expr[c.universe.DefDef] = {
    import c.universe._

    val ClassDef(_, className, _, Template(_, _, fields)) = clazz
    val constructor = fields.collect{ case d: DefDef => d }.find(_.name == termNames.CONSTRUCTOR).get
    val paramss = constructor.vparamss
    val namess = paramss.map(_.map(_.name))

    val expr =
      q"""
        new $className(...$namess) {
          val id = TreeID.id
        }
       """

    val apply =
      q"""
       def apply(...$paramss): $className = $expr
       """

    c.Expr[DefDef](apply)
  }

  def makeCopyMethod(c: whitebox.Context)(clazz: c.universe.ClassDef): c.Expr[c.universe.DefDef] = {
    import c.universe._

    def hasSpecificTrait(exts: List[Tree], name: String*): Boolean = {
      val tpeName = name.map(TypeName.apply)

      exts.exists {
        case Select(_, tpe) => tpeName.contains(tpe)
        case Ident(tpe) => tpeName.contains(tpe)
      }
    }

    val ClassDef(_, className, _, template) = clazz
    val Template(exts, _, defs) = template
    val hasTypeTrait = hasSpecificTrait(exts, "HasType", "Expression")
    val hasSymbolTrait = hasSpecificTrait(exts, "HasSymbol", "Definition")

    val constructor = defs
      .collect{ case method: DefDef => method }
      .find { method => method.name == termNames.CONSTRUCTOR}
      .get

    val params = constructor.vparamss.map(_.map {
      case ValDef(_, name, tpe, _) =>
        val expr = Select(This(typeNames.EMPTY), name)
        ValDef(Modifiers(Flag.PARAM | Flag.DEFAULTPARAM), name, tpe, expr)
    })

    val idents = constructor.vparamss.map(_.map { vdef => Ident(TermName(vdef.name.toString)) })

    val cloneExpr = {
      val root =
        q"""
           new $className(...$idents) {
             override val position = oldPos
             _id = oldID
           }
          """
      val symAttached =
        if(hasSymbolTrait) q"$root.setSymbol(this.symbol)"
        else root

      val typeAttached =
        if(hasTypeTrait) {
          q"$symAttached.setTpe(this.tpe)"
        } else {
          symAttached
        }

      typeAttached
    }


    c.Expr[DefDef](
      q"""
          def copy(...$params): $className = {
            val oldPos = this.position
            val oldID = this._id
            $cloneExpr
          }"""
    )
  }
}
