package tchdl.backend

import tchdl.util._

object NameTemplate {
  def temp: String = "_GEN"
  def variant: String = "_member"
  def enumData: String = "_data"
  def memPointer(mem: String, port: Int): String = s"${mem}_${port}_pointer"
  def memEnDelay(mem: String, port: Int): String = s"${mem}_${port}_cycle"
  def pointerPort(id: Int): String = s"_pointer_$id"
  def pointerWire(id: Int): String = s"__pointer_$id"
  def priorityEnable: String = "_enable"
  def priorityData: String = "_data"
  def concat(names: String*): String = names.mkString("$")
}
