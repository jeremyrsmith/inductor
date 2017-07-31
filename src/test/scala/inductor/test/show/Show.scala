package inductor
package test.show

import inductor.annotation.inductive
import shapeless.{::, HList, HNil, LabelledGeneric, Witness}
import shapeless.labelled.FieldType

abstract class Show[T] {
  def show(t: T): String
}

object Show extends InductiveCompanion1[Show] with ProductGenericCompanion1[Show] {

  def apply[T](implicit inst: Show[T]): Show[T] = inst

  def instance[T](fn: T => String): Show[T] = new Show[T] {
    def show(t: T): String = fn(t)
  }

  def default[T]: Show[T] = Default.asInstanceOf[Show[T]]

  object Default extends Show[Any] {
    def show(t: Any): String = t.toString
  }

  implicit val string: Show[String] = instance(identity)
  implicit val boolean: Show[Boolean] = default
  implicit val byte: Show[Byte] = default
  implicit val short: Show[Short] = default
  implicit val int: Show[Int] = default
  implicit val long: Show[Long] = default
  implicit val float: Show[Float] = default
  implicit val double: Show[Double] = default

  implicit val hnil: Show[HNil] = instance { _ => "" }

  @inductive implicit def hcons[K <: Symbol, H, T <: HList, Impl <: Show[FieldType[K, H] :: T]](implicit
    label: Witness.Aux[K],
    showH: Show[H],
    showT: Show[T]
  ): Show[FieldType[K, H] :: T] = new Show[FieldType[K, H] :: T] {
    def show(t: FieldType[K, H] :: T): String = s"${label.value.name}=${showH.show(t.head)}, ${showT.show(t.tail)}"
  }


  implicit def generic[P <: Product, L <: HList](implicit
    gen: LabelledGeneric.Aux[P, L],
    showL: Show[L]
  ): ProductGeneric[Show[P]] = LabelledProductGeneric {
    new Show[P] {
      def show(p: P): String = showL.show(gen.to(p))
    }
  }

}
