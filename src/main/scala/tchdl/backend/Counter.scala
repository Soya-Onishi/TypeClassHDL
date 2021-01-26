package tchdl.backend

import tchdl.util.TchdlException._
import scala.collection.mutable

abstract class Counter[T] {
  protected val table: mutable.Map[T, Int] = mutable.Map.empty

  def next(key: T): Name
  def count(key: T): Unit
  def refer(key: T): Option[Name]
  def lock(key: T): Unit
  def copy: Counter[T]
}

class TempCounter extends Counter[Int] {
  protected var max = 0

  def next(key: Int): Name = {
    val nextMax = max + 1
    table(key) = nextMax
    max = nextMax

    Name(s"_TEMP_$nextMax")
  }

  def count(key: Int): Unit = {
    max = max + 1
  }

  def refer(key: Int): Option[Name] = {
    val value = table(key)
    Some(Name(s"_TEMP_$value"))
  }

  def lock(key: Int): Unit = throw new ImplementationErrorException("lock is not allowed to temp counter")

  def copy: Counter[Int] = {
    val _max = this.max
    val _table = this.table.clone()

    new TempCounter {
      max = _max
      override protected val table: mutable.Map[Int, Int] = _table
    }
  }
}

class VariableCounter extends Counter[String] {
  protected val eachMax = mutable.Map.empty[String, Int]
  private val locked = mutable.Set.empty[String]

  def next(key: String): Name = {
    assert(!locked(key), s"[$key] is locked")

    eachMax.get(key) match {
      case Some(count) =>
        table(key) = count + 1
        eachMax(key) = count + 1
        Name(s"${key}_$count")
      case None =>
        table(key) = 0
        eachMax(key) = 0
        Name(s"${key}_0")
    }
  }

  def count(key: String): Unit = {
    eachMax.get(key) match {
      case Some(count) => eachMax(key) = count + 1
      case None if locked(key) => // nothing to do
      case None => eachMax(key) = 0
    }
  }

  def refer(key: String): Option[Name] = {
    table.get(key) match {
      case Some(count) => Some(Name(s"${key}_$count"))
      case None if locked(key) => Some(Name(key))
      case None => None
    }
  }

  def lock(key: String): Unit = {
    locked += key
  }

  def copy: Counter[String] = {
    val _table = this.table.clone()
    val _eachMax = this.eachMax.clone()

    new VariableCounter {
      override protected val table: mutable.Map[String, Int] = _table
      override protected val eachMax: mutable.Map[String, Int] = _eachMax
    }
  }
}

