package inductor

import inductor.macros.InductorMacros

import scala.annotation.StaticAnnotation


trait Inductive[T] {
  def value: T
}

object Inductive {


  //def apply[T](inst: => T): Inductive[T]

}
