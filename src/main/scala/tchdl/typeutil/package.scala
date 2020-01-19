package tchdl

package object typeutil {
  type Not[A] = A => Nothing
  type And[A, B] = A with B
  type Or[A, B] = Not[Not[A] And Not[B]]
}
