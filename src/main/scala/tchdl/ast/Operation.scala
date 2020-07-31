package tchdl.ast

trait Operation {
  def toInterface: String
  def toMethod: String
  def toOperator: String
  def isCommutative: Boolean
}

object Operation {
  case object Add extends Operation {
    override def toInterface: String = "Add"
    override def toMethod: String = "add"
    override def toOperator: String = "+"
    override def isCommutative: Boolean = true
  }

  case object Sub extends Operation {
    override def toInterface: String = "Sub"
    override def toMethod: String = "sub"
    override def toOperator: String = "-"
    override def isCommutative: Boolean = false
  }

  case object Mul extends Operation {
    override def toInterface: String = "Mul"
    override def toMethod: String = "mul"
    override def toOperator: String = "*"
    override def isCommutative: Boolean = true
  }

  case object Div extends Operation {
    override def toInterface: String = "Div"
    override def toMethod: String = "div"
    override def toOperator: String = "/"
    override def isCommutative: Boolean = false
  }

  case object Or extends Operation {
    override def toInterface: String = "Or"
    override def toMethod: String = "or"
    override def toOperator: String = "|"
    override def isCommutative: Boolean = true
  }

  case object And extends Operation {
    override def toInterface: String = "And"
    override def toMethod: String = "and"
    override def toOperator: String = "&"
    override def isCommutative: Boolean = true
  }

  case object Xor extends Operation {
    override def toInterface: String = "Xor"
    override def toMethod: String = "xor"
    override def toOperator: String = "^"
    override def isCommutative: Boolean = true
  }

  case object Eq extends Operation {
    override def toInterface: String = "Eq"
    override def toMethod: String = "equal"
    override def toOperator: String = "=="
    override def isCommutative: Boolean = true
  }

  case object Ne extends Operation {
    override def toInterface: String = "Eq"
    override def toMethod: String = "notEqual"
    override def toOperator: String = "!="
    override def isCommutative: Boolean = true
  }

  case object Ge extends Operation {
    override def toInterface: String = "Ord"
    override def toMethod: String = "greaterEqual"
    override def toOperator: String = "<="
    override def isCommutative: Boolean = false
  }

  case object Gt extends Operation {
    override def toInterface: String = "Ord"
    override def toMethod: String = "greaterThan"
    override def toOperator: String = "<"
    override def isCommutative: Boolean = false
  }

  case object Le extends Operation {
    override def toInterface: String = "Ord"
    override def toMethod: String = "lessEqual"
    override def toOperator: String = ">="
    override def isCommutative: Boolean = false
  }

  case object Lt extends Operation {
    override def toInterface: String = "Ord"
    override def toMethod: String = "lessThan"
    override def toOperator: String = ">"
    override def isCommutative: Boolean = false
  }

  case object Shr extends Operation {
    override def toInterface: String = "Shr"
    override def toMethod: String = "shr"
    override def toOperator: String = ">>"
    override def isCommutative: Boolean = false
  }

  case object Shl extends Operation {
    override def toInterface: String = "Shl"
    override def toMethod: String = "shl"
    override def toOperator: String = "<<"
    override def isCommutative: Boolean = false
  }

  case object DynShr extends Operation {
    override def toInterface: String = "DynShr"
    override def toMethod: String = "dynShr"
    override def toOperator: String = ">>>"
    override def isCommutative: Boolean = false
  }

  case object DynShl extends Operation {
    override def toInterface: String = "DynShl"
    override def toMethod: String = "dynShl"
    override def toOperator: String = "<<<"
    override def isCommutative: Boolean = false
  }

  case object Neg extends Operation {
    override def toInterface: String = "Neg"
    override def toMethod: String = "neg"
    override def toOperator: String = "-"
    override def isCommutative: Boolean = false
  }

  case object Not extends Operation {
    override def toInterface: String = "Not"
    override def toMethod: String = "not"
    override def toOperator: String = "!"
    override def isCommutative: Boolean = false
  }
}
