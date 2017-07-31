package inductor

trait InductiveCompanion1[T[_]] {
  implicit def fromInductive[A](implicit inductive: Inductive[T[A]]): T[A] = ???
}
