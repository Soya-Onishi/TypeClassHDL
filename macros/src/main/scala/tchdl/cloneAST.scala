package tchdl

import scala.reflect.macros.whitebox
import scala.language.experimental.macros
import scala.annotation.StaticAnnotation
import scala.annotation.compileTimeOnly

@compileTimeOnly("enable macro paradise to expand macro annotations")
class cloneAST extends StaticAnnotation {
  def macroTransform(annottees: Any*): Any = macro CloneASTMacro.impl
}

object CloneASTMacro {
  def impl(c: whitebox.Context)(annottees: c.Expr[Any]*): c.Expr[Any] = {
    import c.universe._

    def hasSpecificTrait(exts: List[Tree], name: TypeName*): Boolean = {
      exts.exists {
        case Select(_, tpe) => name.contains(tpe)
        case Ident(tpe) => name.contains(tpe)
      }
    }

    val (cdef: ClassDef) :: _ = annottees.map(_.tree).toList
    val ClassDef(mods, className, tps, template) = cdef
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
      val root = q"${Ident(TermName(className.toString))}.apply(...$idents)"
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

    val cloneDef =
      q"""
        def copy(...$cloneParams): $className = $cloneExpr
       """

    val addedTemplate = Template(exts, self, defs ::: List(cloneDef))
    val addedClassDef = ClassDef(mods, className, tps, addedTemplate)

    c.Expr[ClassDef](addedClassDef)
  }
}
