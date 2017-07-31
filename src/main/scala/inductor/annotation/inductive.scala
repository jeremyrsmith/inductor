package inductor.annotation

import inductor.macros.InductorMacros

import scala.annotation.StaticAnnotation

class inductive extends StaticAnnotation {
  def macroTransform(annottees: Any*): Any = macro InductorMacros.expandInductive
}
