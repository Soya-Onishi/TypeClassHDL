package tchdl.backend

import tchdl.util.TchdlException._
import scala.annotation.tailrec
import scala.collection.mutable

abstract class StackFrame {
  protected def parent: StackFrame

  private val scope: mutable.Map[Name, Instance] = mutable.Map.empty
  protected val namer: FirrtlNamer
  val lookupThis: Option[Instance]
  val isBlockStack: Boolean

  def next(name: String): Name = {
    namer.variable.next(name)

    if (parent != null)
      parent.count(name)

    refer(name)
  }

  def next(id: Int): Name = {
    namer.temp.next(id)

    if (parent != null)
      parent.count(id)

    refer(id)
  }

  def refer(name: String): Name = namer.variable.refer(name) match {
    case Some(name) => name
    case None if isBlockStack => parent.refer(name)
    case None => throw new ImplementationErrorException(s"there is no count or lock for [$name]")
  }

  def refer(id: Int): Name = namer.temp.refer(id).get

  def lock(name: String): Unit = namer.variable.lock(name)

  @tailrec private def count(name: String): Unit = {
    namer.variable.count(name)

    if (parent != null)
      parent.count(name)
  }

  @tailrec private def count(id: Int): Unit = {
    namer.temp.count(id)

    if (parent != null)
      parent.count(id)
  }

  def lookup(name: Name): Instance = scope.get(name) match {
    case Some(instance) => instance
    case None if isBlockStack => parent.lookup(name)
    case None => throw new ImplementationErrorException(s"instance must be there (name: ${name.toString})")
  }

  def append(name: Name, instance: Instance): Unit = {
    scope(name) = instance
  }
}

object StackFrame {
  def apply(thisTerm: Instance): StackFrame = {
    new StackFrame {
      override val namer = new FirrtlNamer
      override val parent = null
      override val lookupThis = Some(thisTerm)
      override val isBlockStack = false
    }
  }

  def apply(parent: StackFrame, thisTerm: Option[Instance], isBlockStack: Boolean): StackFrame = {
    val _parent = parent
    val _blkStack = isBlockStack

    new StackFrame {
      override val namer = _parent.namer.copy
      override val parent = _parent
      override val lookupThis = thisTerm
      override val isBlockStack = _blkStack
    }
  }
}

class FirrtlNamer {
  val temp: Counter[Int] = new TempCounter
  val variable: Counter[String] = new VariableCounter

  def copy: FirrtlNamer = {
    val _temp = this.temp.copy
    val _variable = this.variable.copy

    new FirrtlNamer {
      override val temp = _temp
      override val variable = _variable
    }
  }
}