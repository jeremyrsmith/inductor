package inductor

import inductor.macros.InductorMacros

import scala.annotation.StaticAnnotation


trait Inductive[T] {
  def value: T
}

object Inductive {

  // TODO: should wrap inductive calls with Inductive[] type to intercept them (like LabelledProductGeneric does)
  // this would allow optimized inductive instances to be made even when we're directly using HList types
  //def apply[T](inst: => T): Inductive[T]

}
