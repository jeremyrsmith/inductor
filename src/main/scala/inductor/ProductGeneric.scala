package inductor

import shapeless.LabelledGeneric

trait ProductGeneric[T] {
  def value: T
}

