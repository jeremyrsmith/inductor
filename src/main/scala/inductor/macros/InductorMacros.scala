package inductor
package macros


import shapeless.{CaseClassMacros, SingletonTypeUtils}

import scala.collection.immutable.Queue
import scala.reflect.macros.whitebox

class InductorMacros(val c: whitebox.Context) extends CaseClassMacros with SingletonTypeUtils {
  import c.universe._

  private val Inductive = weakTypeOf[Inductive[_]].typeConstructor
  private val implTreeAnnot = weakTypeOf[implTree]
  private val WitnessAux = weakTypeOf[shapeless.Witness.Aux[_]].typeConstructor
  private val ScalaSymbol = weakTypeOf[scala.Symbol]
  private val HCons = weakTypeOf[shapeless.::[_, _]].typeConstructor
  private val HConsObj = reify(shapeless.::).tree


  def expandInductive(annottees: Tree*): Tree = {
    val results = annottees.map {
      case d @ DefDef(mods, name, tParams, paramLists, tpt, rhs) =>
        val annotValue = q"{$d}"//Function(paramLists.head, rhs)
        DefDef(
          mods.mapAnnotations(q"new $implTreeAnnot($annotValue)" :: _),
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
      productGeneric match {
        case Apply(TypeApply(fun@HasImplTree(DefDef(_, _, implTypeArgs, List(implImplicitParams), _, Apply(TypeApply(Select(Select(_, TermName(pgCall)), TermName("apply")), _), List(implTree)))), typeArgTrees), args) =>
          val isLabelled = pgCall == "LabelledProductGeneric"
          val typeArgs = typeArgTrees.map(_.tpe.dealias)

          val fields = fieldsOf(A)
          val fieldTypes = if (isLabelled)
            fields.map((mkFieldTpe _).tupled)
          else
            fields.map(_._2)

          val inductive = mkHListTpe(fieldTypes)
          val hlistImplicitType = appliedType(
            T.typeConstructor, productGeneric.tpe.typeArgs.head.typeArgs.map {
              case A => inductive
              case other => other
            })

          // find the argument that's the appropriate shapeless.[Labelled]Generic type
          val genericType = if (isLabelled)
            appliedType(weakTypeOf[shapeless.LabelledGeneric.Aux[_, _]].typeConstructor, A, inductive)
          else
            appliedType(weakTypeOf[shapeless.Generic.Aux[_, _]].typeConstructor, A, inductive)


          val genericArg = (implImplicitParams zip args).find {
            case (vParam, arg) => arg.tpe =:= genericType
          }.getOrElse {
            c.abort(c.enclosingPosition, s"Derivation ${fun.symbol} does not have an implicit argument of type $genericType")
          }

          val genericName = genericArg._1.name

          val hlistImplicitArg = (implImplicitParams zip args).find {
            case (vParam, arg) => arg.tpe =:= hlistImplicitType
          }.getOrElse {
            c.abort(c.enclosingPosition, s"Derivation ${fun.symbol} does not have an implicit argument of type $hlistImplicitType")
          }

          val inlined = inlineInductive(hlistImplicitArg._2)

          val argIsInductive = args.map {
            arg => arg.tpe =:= genericType || arg.tpe =:= hlistImplicitType
          }

          val treeCopier = new Transformer {
            override val treeCopy: TreeCopier = c.universe.newStrictTreeCopier
          }

          val implCopy = c.typecheck(treeCopier.transform(c.untypecheck(implTree)))

          val eliminatedImplTree = c.internal.substituteTypes(
            eliminateStableArgs(implCopy, implImplicitParams, argIsInductive, args),
            implTypeArgs.map(_.symbol),
            typeArgs)

          val inductiveName = hlistImplicitArg._1.name

          val inlinedMembers = implementationMembers(inlined.tpe, inlined)._1.map {
            dd => dd.name -> dd
          }.toMap

          /*
            Eliminate gen.from and gen.to

            Whenever we see gen.to, we're going to the HList type. We should be passing that HList to an inductive
            call. So we just inline that inductive call, and replace head | tail.head etc with field accessors.

            Similarly, whenever we see gen.from, we're going from the HList type to the product type. This means what
            we're passing to gen.from must be the result of an inductive call. This could also be inlined, but it's more
            difficult because this usually means the HList result has been lifted into some kind of functor and we're
            mapping over it with gen.from. I haven't dealt with this yet (TODO)
          */
          val eliminateGenTo = new Transformer {
            override def transform(tree: Tree): Tree = {
              tree match {
                case MethodCall(Ident(`inductiveName`), methodName, tParams, argLists) if (inlinedMembers contains methodName) && argLists.flatten.exists {
                  case Apply(Select(Ident(`genericName`), TermName("to")), _) => true
                  case _ => false
                } =>
                  val member = inlinedMembers(methodName)
                  val flatArgs = member.vparamss.zip(argLists).flatMap {
                    case (methodParams, methodArgs) => methodParams zip methodArgs
                  }

                  val argTrees = flatArgs.map {
                    case (methodParam, methodArg) => methodParam.name -> methodArg
                  }.toMap

                  val (prodArg, prodTree) = flatArgs.collectFirst {
                    case (methodParam, Apply(Select(Ident(`genericName`), TermName("to")), List(prod))) => methodParam.name -> prod
                  }.get

                  val transformer = new Transformer {

                    object HeadsyTailsy {
                      def unapply(tree: Tree): Option[Int] = tree match {
                        case Select(HeadsyTailsy(i), TermName("head")) => Some(i)
                        case Select(HeadsyTailsy(i), TermName("tail")) => Some(i + 1)
                        case Ident(`prodArg`) => Some(0)
                        case _ => None
                      }
                    }

                    override def transform(tree: Tree): Tree = {
                      val result = tree match {
                        case HeadsyTailsy(i) if i == fields.length => c.typecheck(reify(shapeless.HNil).tree)
                        case HeadsyTailsy(i) =>
                          c.typecheck(Typed(Select(prodTree, fields(i)._1), TypeTree(fields(i)._2)))
                        case Ident(name: TermName) if argTrees contains name =>
                          argTrees(name)
                        case other => super.transform(other)
                      }
                      result
                    }
                  }
                  val result = transformer.transform(member.rhs)
                  result

                case dd: DefDef => c.typecheck(super.transform(dd))
                case other => super.transform(other)
              }
            }
          }

          val result = eliminateGenTo.transform(eliminatedImplTree)

          val typed = try c.typecheck(result) catch {
            case err: Throwable =>
              val e = err
              println(e)
              throw e
          }
          typed
      }
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
        def method(param: Bar :: Baz :: Int :: HNil): Result =
          Something.bar(param.head) combine Something.baz(param.tail.head) combine Something.int(param.tail.tail.head) combine Something.hnil(param.tail.tail.tail)
      }

    The strategy for this is to go through all of the parameters to the given tree, and recurse into any inductive calls within those parameters until
    reaching leaves. Then as we walk back up the recursion tree, we create a new implementation at each step that inlines the implementations of the
    arguments it has, and return a new tree with that implementation. So after the first step we would have:

      new Foo[Baz :: Int :: HNil] {
        def method(param: Baz :: Int :: HNil): Result =
          Something.baz(param.head) combine Something.int(param.tail.head) combine Something.hnil(param.tail.tail)
      }


    Where the `Something.int(_1) combine _` comes from inlining the argument (Something.int) into the implementation of Foo.hcons (i.e. param.head)
    and the HNilResult comes directly from the implementation of Foo.hnil.

    From there, it's not hard to imagine repeating that for the second step - inlining that implementation further with in the same way given the
    parameter of Something.baz - and so forth.
  */
  private def inlineInductive(derived: Tree): Tree = {
    val T = derived.tpe
    derived match {
      case Apply(TypeApply(fun @ HasImplTree(impl @ DefDef(_, _, implTypeArgs, List(implImplicitParams), implTypeTree, implTree)), typeArgs), args) =>
        inlineInductiveDerivation(T, fun, impl, implTypeArgs, implImplicitParams, implTypeTree, implTree, typeArgs.map(_.tpe.dealias), args)
      case Apply(fun @ HasImplTree(impl @ DefDef(_, _, Nil, List(implImplicitParams), implTypeTree, implTree)), args) =>
        inlineInductiveDerivation(T, fun, impl, Nil, implImplicitParams, implTypeTree, implTree, Nil, args)
    }
  }

  private def inlineInductiveDerivation(T: Type, fun: Tree, impl: DefDef, implTypeArgs: List[TypeDef], implImplicitParams: List[ValDef], implTypeTree: Tree, implTree: Tree, typeArgs: List[Type], args: List[Tree]): Tree = {

    // which arguments are further inductive?
    val argIsInductive = args.map {
      case Apply(HasImplTree(_), _) => true
      case a @ Apply(_, _) if a.tpe.typeConstructor <:< T.typeConstructor =>
        c.warning(fun.pos, s"Inductive implementation ${fun.symbol.fullName} is not annotated with @inductive; the inductive derivation won't be optimized")
        c.abort(c.enclosingPosition, "Not inductive")
      case _ => false
    }

    val treeCopier = new Transformer {
      override val treeCopy: TreeCopier = c.universe.newStrictTreeCopier
    }

    val implCopy = c.typecheck(c.untypecheck(treeCopier.transform(implTree)))

    // all remaining arguments should be stable, public implicits
    // eliminate references to those arguments in the implementation and substitute type arguments
    val eliminatedImplTree = c.internal.substituteTypes(
      eliminateStableArgs(implCopy, implImplicitParams, argIsInductive, args),
      implTypeArgs.map(_.symbol),
      typeArgs)

    val inductiveMembers = (implImplicitParams zip argIsInductive zip args).collect {
      case ((param, true), arg) =>
        param.name -> implementationMembers(arg.tpe, inlineInductive(arg))._1
    }.toMap

    val result =
      eliminateInductiveCalls(eliminatedImplTree, inductiveMembers)

    try {
      c.typecheck(result)
    } catch {
      case err: Throwable =>
        val e = err
        println(e)
        throw e
    }
  }


  private def eliminateInductiveCalls(implTree: Tree, inductiveMembers: Map[TermName, List[DefDef]]): Tree = {
    val transform = new Transformer {
      override def transform(tree: Tree): Tree = tree match {
        case MethodCall(Ident(targetName: TermName), methodName, tParams, paramLists) if inductiveMembers contains targetName =>
          // TODO: this won't respect overloaded methods - be more rigorous in finding the precise method to inline
          val targetMethod = inductiveMembers(targetName).find(_.name.toString == methodName.toString).getOrElse {
            c.abort(tree.pos, s"Couldn't inline method $methodName")
          }

          val methodArgs = targetMethod.vparamss.zip(paramLists).map {
            case (methodParams, callParams) => methodParams.zip(callParams)
          }.flatMap {
            tups => tups.map {
              case (vd, impl) =>
                vd.name -> impl
            }
          }.toMap

          // TODO: is it safe to assume that the arguments are referentially transparent?
          // Right now there is no memoization happening, so the argument trees must not side effect.

          val inliner = new Transformer {
            override def transform(tree: Tree): Tree = tree match {
              case Ident(name: TermName) if methodArgs contains name => methodArgs(name)
              case other => super.transform(other)
            }
          }

          inliner.transform(targetMethod.rhs)

        case other => super.transform(other)
      }
    }
    transform.transform(implTree)
  }

  private def eliminateStableArgs(implTree: Tree, implImplicitParams: List[ValDef], argIsInductive: List[Boolean], args: List[Tree]): Tree = {
    val eliminatedArgs = implImplicitParams.zip(argIsInductive.zip(args)).collect {
      // eliminate witnesses
      case (v @ ValDef(mods, name, tpt, rhs), (false, tree)) if tree.tpe != null && tree.tpe.typeConstructor <:< WitnessAux && tree.tpe.typeArgs.length == 1 =>
        tree.tpe.typeArgs.head match {
          case SingletonSymbolType(str) => name -> c.typecheck(q"$str")
          case ConstantType(const) => name -> c.typecheck(q"$const")
        }

      // eliminate stable typeclass instance refs and other static references
      case (v @ ValDef(mods, name, tpt, rhs), (false, s @ Select(qual, sel)))
        if qual.symbol.isModule && qual.symbol.isPublic && s.symbol.isTerm && s.symbol.isPublic && s.symbol.asTerm.isStable =>
        name -> s

      case (param, (false, arg)) =>
        c.warning(arg.pos, s"Supplied non-inductive implicit $arg is not stable; cannot proceed with optimization")
        c.abort(c.enclosingPosition, "Cannot optimize due to non-stable, non-inductive implicit")
    }.toMap

    val transform = new Transformer {
      override def transform(tree: Tree): Tree = tree match {
        case Select(v @ Select(i @ Ident(name: TermName), TermName("value")), TermName("name"))
          if i.tpe != null && i.tpe.typeConstructor <:< WitnessAux && (eliminatedArgs contains name) && (v.tpe <:< ScalaSymbol) => eliminatedArgs(name)
        case Select(i @ Ident(name: TermName), TermName("value"))
          if i.tpe != null && i.tpe.typeConstructor <:< WitnessAux && (eliminatedArgs contains name) => eliminatedArgs(name)
        case Ident(name: TermName) if eliminatedArgs contains name => eliminatedArgs(name)
        case other => super.transform(other)
      }
    }

    transform.transform(implTree)
  }

  private def implementationMembers(T: Type, implTree: Tree): (List[DefDef], List[TypeDef]) = implTree match {
    case Block(List(ClassDef(_, _, _, Template(_, _, implDecls))), _) => (
      implDecls.collect {
        case dd @ DefDef(mods, name, tParams, vParams, tpt, rhs)
          if !dd.symbol.isConstructor && T.decl(dd.name).isMethod =>
          val sym = T.decl(dd.name).asMethod
          val symTyp = sym.typeSignatureIn(T)
          val typed = DefDef(mods, name, tParams,
            vParams.zip(symTyp.paramLists).map {
              case (implParams, symParams) => implParams zip symParams map {
                case (implParam, symParam) =>
                  c.internal.valDef(symParam)
              }
            },
            TypeTree(symTyp.finalResultType),
            rhs
          )
          try {
            c.typecheck(typed) match {
              case dd: DefDef => dd
              case other => c.abort(c.enclosingPosition, s"Unexpected tree type ${other.getClass.getSimpleName} after untypechecking DefDef")
            }
          } catch {
            case err: Throwable =>
              val e = err
              println(e)
              throw e
          }
      },
      implDecls.collect {
        case td: TypeDef if T.member(td.name).isType => td
      }
    )
  }

  private def inductivePattern(arg: Tree): (Tree => Match, List[TermName]) = {
    val argTyp = arg.tpe
    argTyp match {
      case BinaryInductiveType(matchFnFn) => matchFnFn(arg)
    }
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
      annots.find(_.tree.tpe <:< implTreeAnnot).map(_.tree).map {
        case Apply(_, List(Block(List(defdef: DefDef), _))) => defdef
        case other => c.abort(other.pos, "Malformed @implTree annotation")
      }
    }
  }

  object BinaryInductiveType {
    def unapply(typ: Type): Option[Tree => ((Tree => Match), List[TermName])] = typ.typeArgs match {
      case List(first, second) if typ.companion.typeSymbol.isModule =>
        val companionType = typ.companion
        val companion = companionType.termSymbol

        unapply(second).map {
          fn => fn andThen {
            case (prevMatchFn, names) =>
              val name = TermName(c.freshName())
              val matchFn = prevMatchFn andThen {
                case Match(sel, List(cq"$pat => $body")) =>
                  Match(sel, List(cq"$companion($name, $pat) => $body"))
              }
              matchFn -> (name :: names)
          }
        }

      case Nil => Some {
        selector =>
          val name = TermName(c.freshName())
          ((body: Tree) => Match(q"$selector", List(cq"$name @ _ => $body"))) -> List(name)
      }
    }
  }

  object MethodCall {
    def unapply(tree: Tree): Option[(Tree, TermName, List[Type], List[List[Tree]])] = tree match {
      case Apply(MethodCall(target, name, tParams, paramLists), paramList) => Some((target, name, tParams, paramLists :+ paramList))
      case Apply(Select(target, name: TermName), params) => Some((target, name, Nil, List(params)))
      case TypeApply(Select(target, name: TermName), typeParams) => Some((target, name, typeParams.map(_.tpe), Nil))
      case _ => None
    }
  }

}
