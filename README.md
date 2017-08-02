# inductor

This is a proof-of-concept for optimizing the runtime performance of inductively derived typeclasses, particularly those
that arise when using [shapeless](https://github.com/milessabin/shapeless).

## TLDR

Assuming you're already familiar with shapeless, here's what inductor does.

```scala
import inductor._
import shapeless._
import shapeless.labelled.FieldType

abstract class Show[T] {
  def show(t: T): String
}

object Show extends InductiveCompanion1[Show] with ProductGenericCompanion1[Show] {

  // .. instances for leaf types and for `HNil`

  @inductive implicit def hcons[K <: Symbol, H, T <: HList, Impl <: Show[FieldType[K, H] :: T]](implicit
    label: Witness.Aux[K],
    showH: Show[H],
    showT: Show[T]
  ): Show[FieldType[K, H] :: T] = new Show[FieldType[K, H] :: T] {
    def show(t: FieldType[K, H] :: T): String =
      label.value.name + "=" + showH.show(t.head) + ", " + showT.show(t.tail)
  }
  
  @inductive implicit def generic[P <: Product, L <: HList](implicit
    gen: LabelledGeneric.Aux[P, L],
    showL: Show[L]
  ): ProductGeneric[Show[P]] = LabelledProductGeneric {
    new Show[P] {
      def show(p: P): String = showL.show(gen.to(p))
    }
  }

}

case class Foo(a: Int, b: String, c: Boolean)
val inst = implicitly[Show[Foo]]
```

With regular generic derivation, `inst` contains something like

```scala
new Show[Foo] {
  def show(p: Foo): String = new Show[FieldType['a, Int] :: FieldType['b, Int] :: FieldType['c, Int] :: HNil] {
    def show(t: FieldType['a, Int] :: FieldType['b, Int] :: FieldType['c, Int] :: HNil) =
      new Witness { type T = 'a; val value = 'a }.value.name + "=" + Show.int.show(t.head) + ", " +
        new Show[FieldType['b, Int] :: FieldType['c, Int] :: HNil] {
          def show(t: FieldType['b, Int] :: FieldType['c, Int] :: HNil) =
            new Witness { type T = 'b; val value = 'b }.value + "=" + Show.int.show(t.head) + ", " +
              new Show[FieldType['c, Int] :: HNil] {
                def show(t: FieldType['c, Int] :: HNil) =
                  new Witness { type T = 'c; val value = 'c }.value + "=" + Show.bool.show(t.head) + ", " +
                    Show.hnil.show(t.tail)
              }.show(t.tail)
        }.show(t.tail)
  }.show(
    new LabelledGeneric[Foo] {
      // gobbledygook here
    }.to(p)
  )
}
```

It contains a lot of overhead. Not terrible, and certainly worth the clean, type-oriented experience for the user of
your typeclass. But that overhead can be a killer in a tight loop, as explained below.

Because of the `@inductive` annotation, what `inst` actually looks like after the inductor treatment is:

```scala
new Show[Foo] {
  def show(p: Foo): String =
    "a" + "=" + Show.int.show(p.a) + ", " +
    "b" + "=" + Show.string.show(p.b) + ", " +
    "c" + "=" + Show.bool.show(p.c) + ", " + Show.hnil.show(HNil)
}
```

Which is far more friendly to tight loops. We could even `@inductive` the individual instances and have them inlined,
but if we get it to this point then the JVM will generally take care of the rest.

## Motivation

A typical use of shapeless is as follows:

* Define a typeclass which will do interesting stuff based on its type argument(s).
* Define how that typeclass works for a variety of leaf types (typically primitives or other common Java types).
* Define how that typeclass works for any product type (i.e. `case class`), given that the members of the product type
  each in turn define what to do with that member's type. This is where shapeless's magic comes in, and it's done by:
  * Defining a generic derivation using `[Labelled]Generic`. This gets you from the product type to a sort of fixed-point
    binary recursive type, terminated by `HNil`.
  * Now you can define a base case for the derivation, by defining a typeclass instance for `HNil`.
  * And you can define one or more recursive cases for the derivation, by focusing on the head of the `HList` type and
    delegating the logic for the tail of the `HList` type recursively until you reach the base case.

See above under "TLDR" for what this looks like for a simple (useless) typeclass.

This is really neat, but it has performance implications: we have to construct all of these inductive instances, and
usually other auxiliary things like `Witness`es. Then, we have to recursively call methods on each of these instances.
The recursion gets deeper as the case class gains members.

Now, *if* the JVM was smart enough to inline all of the calls, then constructing the instances wouldn't be such a big
deal. Or, *if* the Scala compiler was smart enough to do that - again, we're happy.

But neither of these things is true. And it's frustrating, because we have enough information at compile time to
essentially unroll the loop. And with a little help, we could also have enough information to inline the recursive
calls. Inductor does this at the source level using macros.

The goal for inductor is that it could enable the usage of shapeless-based APIs for cases in which tight loop performance
is paramount - like machine learning.

## Proof-of-concept

Obviously, this is missing a lot of things. I hope to add them and make it robust. Maybe you can help? Of course, the
real hope would be that improvements to the Scala compiler would obviate the usefulness of something like inductor.
But in the meantime, here are the things that are missing and limited:

* Only works for `* -> *`-kinded typeclasses (dependent types should work, though)
* Can't eliminate `gen.from` calls (these would actually cause the optimization to fail at this point)
* Requires a `@inductive` annotation on all the inductive implicits - this is needed in order to keep the tree around
  after compile, so that we can do source-level inlining later.
* You won't be able to use shapeless's out-of-the-box typeclasses in your derivation; it has to be from base principles
  (maybe inductor could offer inductive versions of them)
* Terrible messy code (getting gnarly macros to work the way you want without crashing the compiler is an exercise in trial and error)

## Help out

If you're interested in the concept, please give it a try! Make PRs and report issues (which I'm sure are plentiful).