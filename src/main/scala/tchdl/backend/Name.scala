package tchdl.backend

case class Name(name: String) {
  override def hashCode(): Int = name.hashCode
}
