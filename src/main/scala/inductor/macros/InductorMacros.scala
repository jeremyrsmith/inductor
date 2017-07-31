package inductor
package macros


import shapeless.{CaseClassMacros, SingletonTypeUtils}

import scala.collection.immutable.Queue
import scala.reflect.macros.whitebox

class InductorMacros(val c: whitebox.Context) extends CaseClassMacros with SingletonTypeUtils {
  import c.universe._

  private val Inductive = weakTypeOf[Inductive[_]].typeConstructor
  private val implTree = weakTypeOf[implTree]
  private val WitnessAux = weakTypeOf[shapeless.Witness.Aux[_]].typeConstructor
  private val ScalaSymbol = weakTypeOf[scala.Symbol]
  private val HCons = weakTypeOf[shapeless.::[_, _]].typeConstructor
  private val HConsObj = reify(shapeless.::).tree


  def expandInductive(annottees: Tree*): Tree = {
    val results = annottees.map {
      case d @ DefDef(mods, name, tParams, paramLists, tpt, rhs) =>
        val annotValue = q"{$d}"//Function(paramLists.head, rhs)
        DefDef(
          mods.mapAnnotations(q"new $implTree($annotValue)" :: _),
          name, tParams, paramLists, tpt, rhs
        )
      case other => other
    }
    val result =
      q"""{
        ..$results
        ()
      }"""
    //c.abort(c.enclosingPosition, "not yet")
    result
  }


  def fromProductGeneric[A : WeakTypeTag, T : WeakTypeTag](productGeneric: Tree): Tree = {
    val T = weakTypeOf[T]
    val A = weakTypeOf[A]
    if(isProduct(A)) {
      val fields = fieldsOf(A)
      val fieldTypes = fields.map((mkFieldTpe _).tupled)
      val inductive = mkHListTpe(fieldTypes)
      val hlistImplicitType = appliedType(T.typeConstructor, productGeneric.tpe.typeArgs.head.typeArgs.map {
        case A => inductive
        case other => other
      })

      val hlistImplicit = c.inferImplicitValue(hlistImplicitType)
      val inlined = inlineInductive(hlistImplicit)
      println(hlistImplicit)
      c.abort(c.enclosingPosition, "not ready yet")
    } else {
      c.abort(c.enclosingPosition, "Not a product type")
    }
  }

  /*
    Receives a tree like Foo.hcons(something = Something.bar, prev = Foo.hcons(something = Something.baz, prev = Foo.hcons(Something.int, Foo.hnil)))
    Where Foo.hcons returns something like

      new Foo[Bar :: Baz :: Int :: HNil] {
        def method(param: Bar :: Baz :: Int :: HNil): Result = something(param.head) combine prev.method(param.tail)
      }

    The result should be a tree of an implementation of Foo[Bar :: Baz :: Int :: HNil] that inlines all of the inductive
    instances, like

      new Foo[Bar :: Baz :: Int :: HNil] {
        def method(param: Bar :: Baz :: Int :: HNil): Result = param match {
          case _1 :: _2 :: _3 :: HNil => Something.bar(_1) combine Something.baz(_2) combine Something.int(_3) combine HNilResult
        }
      }

    The strategy for this is to go through all of the parameters to the given tree, and recurse into any inductive calls within those parameters until
    reaching leaves. Then as we walk back up the recursion tree, we create a new implementation at each step that inlines the implementations of the
    arguments it has, and return a new tree with that implementation. So after the first step we would have:

      Foo.hcons(
        something = Something.bar,
        prev = Foo.hcons(
          something = Something.baz,
          prev = new Foo[Int :: HNil] {
            def method(param: Int :: HNil): Result = {
              case _1 :: HNil => Something.int(_1) combine HNilResult
            }
          }
        )
      )

    Where the `Something.int(_1) combine _` comes from inlining the argument (Something.int) into the implementation of Foo.hcons (i.e. param.head)
    and the HNilResult comes directly from the implementation of Foo.hnil.

    From there, it's not hard to imagine repeating that for the second step - inlining that implementation further with in the same way given the
    parameter of Something.baz - and so forth.
  */
  private def inlineInductive(current: Tree): Tree = {
    val T = current.tpe
    current match {
      case Apply(fun @ HasImplTree(impl), args) =>

        // replace type arguments in the impl

        // find all the methods and dependent types we have to implement for this type
        val (methods: List[DefDef], types: List[TypeDef]) = impl.rhs match {
          case Block(List(ClassDef(_, _, _, Template(_, _, implDecls))), _) => (
            implDecls.collect {
              case dd @ DefDef(mods, name, tParams, vParams, tpt, rhs)
                if !dd.symbol.isConstructor && T.decl(dd.name).isMethod =>
                  val sym = T.decl(dd.name).asMethod
                  val symTyp = sym.typeSignatureIn(T)
                  val typed = c.internal.defDef(
                    sym,
                    vParams.zip(symTyp.paramLists).map {
                      case (implParams, symParams) => implParams zip symParams map {
                        case (implParam, symParam) =>
                          c.internal.valDef(symParam)
                      }
                    },
                    c.untypecheck(rhs)
                  )
                c.typecheck(typed)
            },
            implDecls.collect {
              case td: TypeDef if T.member(td.name).isType => td
            }
          )
        }

        val inlinedArgs = args.map {
          case inductiveParam @ Apply(HasImplTree(_), _) =>
            true -> inlineInductive(inductiveParam)
          case a @ Apply(inductiveCall, inductiveArgs) if a.tpe.typeConstructor <:< T.typeConstructor =>
            c.warning(current.pos, s"Inductive implementation ${fun.symbol.fullName} is not annotated with @inductive; the inductive derivation won't be optimized")
            c.abort(current.pos, "Not inductive")
          case other => false -> other
        }

        val inlinedMethods = methods.map {
          case DefDef(mods, name, tParams, paramLists, tpt, body) =>
            // match each of the implicit params of the implementation with the argument tree
            val suppliedArgs = impl.vparamss.head.zip(inlinedArgs)

            // inlined implementations
            val inlinedBody = suppliedArgs.filter(_._2._1).foldLeft(body) {
              case (currentBody, (param, (_, paramImpl))) =>
                val paramName = param.name
                paramImpl match {
                  // The inlined value is given as { class $anon extends TC[..] { ... }; new $anon }
                  case Block(List(ClassDef(_, _, _, Template(_, _, paramImplDefs))), _) =>
                    // we want to inline all of the method calls made on this param
                    val paramImplMethods = paramImplDefs.collect {
                      case dd: DefDef => dd
                    }
                    val xf = new Transformer {
                      override def transform(tree: Tree): Tree = tree match {
                        case Apply(s @ Select(Ident(`paramName`), method), methodArgs) if s.symbol.isMethod =>
                          val pid = paramImplDefs
                          val methodImpl = paramImplMethods.find {
                            dd => dd.name == method // TODO: this won't handle overloaded methods correctly
//                              val ss = s
//                              val sTpe = s.tpe
//                              val ddParamTypes = dd.vparamss.map(_.map(_.tpe))
//                              val sParamTypes = s.symbol.typeSignatureIn(s.tpe).paramLists.map(_.map(_.typeSignature))
//                              dd.name == s.symbol.name && ddParamTypes == sParamTypes
                          }
                          methodImpl.collect {
                            case mi if mi.vparamss.length == 1 => // TODO: handle curried methods
                              val applyMatchArgs = mi.vparamss.head.zip(methodArgs)
                              applyArgsMatch(applyMatchArgs, mi.rhs)
                          }.getOrElse(super.transform(tree))
                        case _ => super.transform(tree)
                      }
                    }
                    val result = xf.transform(currentBody)
                    result
                }
                //println(paramImpl)
                //currentBody
            }

            val matchTupleArgs = suppliedArgs.filterNot(_._2._1).map(t => t._1 -> t._2._2)

            // create a reference to each of the args, replacing the implicit argument of the derivation within the body
            val inlinedMatch = applyArgsMatch(matchTupleArgs, inlinedBody)

            val outerMatch = collapseNestedMatches(
              applyArgsMatch(paramLists.flatten.map(vd => vd -> q"${vd.name}: ${vd.tpt}"), inlinedMatch)
            )

            DefDef(mods, name, tParams, paramLists, tpt, outerMatch)
        }

        val inlinedTypes = types.map {
          case TypeDef(mods, name, tParams, rhs) =>
            // substitute any references to the type parameters of the derivation
            // TODO
        }

        val anon = TypeName(c.freshName(T.typeSymbol.name.toString))

        val result =
          q"""
             final class $anon extends $T {
               ..$inlinedMethods
             }
             new $anon
           """

        println(result)

        //c.abort(c.enclosingPosition, "not yet")
        try {
          c.typecheck(result)
          //result
        } catch {
          case err: Throwable =>
            val e = err
            println(err)
            throw err
        }
      case Apply(fun, _) =>
        c.warning(current.pos, s"Inductive implementation ${fun.symbol.fullName} is not annotated with @inductive; the inductive derivation won't be optimized")
        c.abort(current.pos, "Not inductive")

    }
  }

  private def applyArgsMatch(args: List[(ValDef, Tree)], body: Tree): Tree = {

    val eliminatedArgs = args.collect {
      // eliminate witnesses
      case (v @ ValDef(mods, name, tpt, rhs), tree) if tree.tpe != null && tree.tpe.typeConstructor <:< WitnessAux =>
        tree.tpe.typeArgs.headOption.collect {
          case SingletonSymbolType(str) => name -> q"$str"
          case ConstantType(const) => name -> q"$const"
        }
      // eliminate stable typeclass instance refs and other static references
      case (v @ ValDef(mods, name, tpt, rhs), s @ Select(qual, sel))
        if qual.symbol.isModule && qual.symbol.isPublic && s.symbol.isTerm && s.symbol.isPublic && s.symbol.asTerm.isStable =>
          Some(name -> s)
    }.flatten.toMap

    // simplify match construct for HCons args using head and tail
    val hconsArgs = args.collect {
      case (v @ ValDef(mods, name, tpt, rhs), tree) if tpt.tpe != null && tpt.tpe.typeConstructor <:< HCons =>
        name -> (TermName(c.freshName(name.toString + "_head")), TermName(c.freshName(name.toString + "_tail")))
    }.toMap

    val nonEliminatedArgs = args.filterNot { case (vd, _) => eliminatedArgs contains vd.name }

    val simplifiedBody = new Transformer {
      override def transform(tree: Tree): Tree = tree match {
        case Select(v @ Select(i @ Ident(name: TermName), TermName("value")), TermName("name"))
          if i.tpe != null && i.tpe.typeConstructor <:< WitnessAux && (eliminatedArgs contains name) && (v.tpe <:< ScalaSymbol) => eliminatedArgs(name)
        case Select(i @ Ident(name: TermName), TermName("value"))
          if i.tpe != null && i.tpe.typeConstructor <:< WitnessAux && (eliminatedArgs contains name) => eliminatedArgs(name)
        case Select(Ident(name: TermName), TermName("head")) if hconsArgs contains name =>
          Ident(hconsArgs(name)._1)
        case Select(Ident(name: TermName), TermName("tail")) if hconsArgs contains name =>
          Ident(hconsArgs(name)._2)
        case Ident(name: TermName) if eliminatedArgs contains name => eliminatedArgs(name)
        case other => super.transform(other)
      }
    }.transform(body)

    if(nonEliminatedArgs.nonEmpty) {
      val matchPat = pq"""(..${
        nonEliminatedArgs.map {
          case (vd, _) if hconsArgs contains vd.name => pq"$HConsObj(${hconsArgs(vd.name)._1}, ${hconsArgs(vd.name)._2})"
          case (vd, _) => pq"${vd.name}"
        }
      })"""
      val matchCase = cq"$matchPat => $simplifiedBody"
      q"(..${nonEliminatedArgs.map(_._2)}) match { case $matchCase }"
    } else {
      simplifiedBody
    }
  }

  private def collapseNestedMatches(tree: Tree): Tree = tree match {
    case Match(q"(..$sels)", List(CaseDef(pq"(..$pats)", EmptyTree, body))) =>
      val simplified = (sels zip pats).foldLeft(body) {
        case (current, (sel @ Typed(Ident(argName), argTpt), q"$HConsObj(${Bind(headName, _)}, ${Bind(tailName, _)})")) =>
          val ccurrent = current
          val ssel = sel
          val hpat = headName
          val tpat = tailName
          new Transformer {
            override def transform(tree: Tree): Tree = tree match {
              case Ident(`headName`) => Select(Ident(argName), TermName("head"))
              case Ident(`tailName`) => Select(Ident(argName), TermName("tail"))
              case other => super.transform(other)
            }
          }.transform(current)
        case (current, _) => current
      }

//      val simplifiedBody = new Transformer {
//        override def transform(tree: Tree): Tree = tree match {
//          case Ident(`headName`) =>
//        }
//      }

      println(body)
      tree
    case other => other
  }

  private def inlineInductiveArgs(impl: DefDef, args: List[Tree]): Tree = {
    EmptyTree
  }

  def mkLabelledProductGeneric[P : WeakTypeTag, L : WeakTypeTag, ProductTC : WeakTypeTag, HListTC : WeakTypeTag](
    fn: Tree
  ): Tree = fn match {
    case Function(List(labelledGeneric, hlistTc), body) => ???
  }

  object HasImplTree {
    def unapply(tree: Tree): Option[DefDef] = {
      val sym = tree.symbol
      val annots = sym.annotations
      annots.find(_.tree.tpe <:< implTree).map(_.tree).map {
        case Apply(_, List(Block(List(defdef: DefDef), _))) => defdef
        case other => c.abort(other.pos, "Malformed @implTree annotation")
      }
    }
  }

}
