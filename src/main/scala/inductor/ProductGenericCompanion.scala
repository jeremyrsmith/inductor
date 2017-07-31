package inductor

import shapeless.{HList, LabelledGeneric}
import inductor.macros.InductorMacros

trait ProductGenericCompanion1[T[_]] {
  implicit def fromProductGeneric[A <: Product](implicit productGeneric: ProductGeneric[T[A]]): T[A] =
    macro InductorMacros.fromProductGeneric[A, T[A]]

  object LabelledProductGeneric {
    def apply[A](inst: T[A]): ProductGeneric[T[A]] = new ProductGeneric[T[A]] { def value = inst }
    //def apply[P <: Product, L <: HList](fn: LabelledGeneric.Aux[P, L] => T[L] => T[P]): ProductGeneric[T[P]] =
      //macro InductorMacros.mkLabelledProductGeneric[P, L, T[P], T[L]]
  }
}
