package tchdl.backend

import tchdl.util._

object NameTemplate {
  def temp: String                 = "_GEN"
  def enumFlag: String             = "_member"
  def enumData: String             = "_data"
  def pointerPort(id: Int): String = s"_pointer_$id"
  def pointerWire(id: Int): String = s"__pointer_$id"
  def priorityEnable: String       = "_enable"
  def priorityData: String         = "_data"
  def active: String               = "_active"
  def ret: String                  = "_ret"
  def state: String                = "_state"
  def id: String                   = "_id"

  def memPointer(mem: String, port: Int): String = s"${mem}_${port}_pointer"
  def memEnDelay(mem: String, port: Int): String = s"${mem}_${port}_cycle"

  def concat(names: String*): String = names.filterNot(_.isEmpty).mkString(concatCh)
  def concatCh: String = "_"
}
