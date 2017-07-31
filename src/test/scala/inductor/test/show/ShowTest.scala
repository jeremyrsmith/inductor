package inductor.test.show

import org.scalatest.FreeSpec

class ShowTest extends FreeSpec {

  case class Foo(a: Int, b: String, c: Boolean)

  "works" in {
    Show[Foo].show(Foo(10, "ten", true))
  }

}
