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

    def hasSpecificTrait(exts: List[Tree], name: TypeName*): Boolean = {
      exts.exists {
        case Select(_, tpe) => name.contains(tpe)
        case Ident(tpe) => name.contains(tpe)
      }
    }

    val ClassDef(mods, className, tps, template) = clazz
    val Template(exts, self, defs) = template
    val hasTypeTrait = hasSpecificTrait(exts, TypeName("HasType"), TypeName("Expression"))
    val hasSymbolTrait = hasSpecificTrait(exts, TypeName("HasSymbol"), TypeName("Definition"))

    val constructor = defs.find {
      case DefDef(_, name, _, _, _, _) if name == termNames.CONSTRUCTOR => true
      case _ => false
    }.get.asInstanceOf[DefDef]

    val cloneParams = constructor.vparamss.map(_.map {
      case ValDef(_, name, tpe, _) =>
        val expr = Select(This(typeNames.EMPTY), name)
        ValDef(Modifiers(Flag.PARAM | Flag.DEFAULTPARAM), name, tpe, expr)
    })

    val idents = constructor.vparamss.map(_.map {
      case ValDef(_, name, _, _) =>
        Ident(TermName(name.toString))
    })

    val cloneExpr = {
      val root =
        q"""
           new $className(...$idents) {
             val id = originID
           }
          """
      val symAttached =
        if(hasSymbolTrait) {
          q"$root.setSymbol(this.symbol)"
        } else {
          root
        }

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
          def copy(...$cloneParams): $className = {
            val originID = this.id
            $cloneExpr
          }"""
    )
  }
}
