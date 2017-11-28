# **Squid** ― Scala Quoted DSLs

[![Join the chat at https://gitter.im/epfldata-squid/Lobby](https://badges.gitter.im/epfldata-squid/Lobby.svg)](https://gitter.im/epfldata-squid/Lobby?utm_source=badge&utm_medium=badge&utm_campaign=pr-badge&utm_content=badge)



## Introduction

**Squid** (for the approximative contraction of **Sc**ala **Qu**ot**ed** **D**SLs)
is a **metaprogramming** framework 
that facilitates the **type-safe** manipulation of **Scala programs**.
Squid extends multi-stage programming capabilities with support for code inspection and code transformation. It has special support for 
**library-defined optimizations** [[2]](#gpce17) and 
helps with the compilation of **domain-specific languages** (DSL) embedded in Scala [[1]](#scala17).
Squid uses **advanced static typing** techniques to prevent common metaprogramming errors, such as scope extrusion [[3]](#popl18).

<!-- TODO: give concrete application examples to pique curiosity/generate interest -->

**Caution:** Squid is still experimental, and the interfaces it exposes may slightly change in the future. This applies especially to the semi-internal interfaces used to implement intermediate representation backends (the `Base` trait and derived).


<a name="early-example">

## A Short Example

To give a quick taste of Squid's capabilities,
here is a very basic example of program manipulation.
The full source code can be [found here, in the example folder](/example/src/main/scala/example/doc/IntroExample.scala).

Assume we define some library function `foo` as below:

```scala
@embed object Test {
  @phase('MyPhase) // phase specification helps with mechanized inlining
  def foo[T](xs: List[T]) = xs.head
}
```

The `@embed` annotation allows Squid to the see the method implementations inside an object or class, so that they can be inlined later automatically (as shown below) 
–– note that this annotation is _not_ required in general, as non-annotated methods can also be used inside quasiquotes.

What follows is an example REPL session demonstrating some program manipulation
using Squid quasiquotes, 
transformers and first-class term rewriting:

```scala
// Syntax `code"t"` represents term `t` in some specified intermediate representation
> val pgrm0 = code"Test.foo(1 :: 2 :: 3 :: Nil) + 1"
pgrm0: ClosedCode[Double] = code"""
  val x_0 = Test.foo[scala.Int](scala.collection.immutable.Nil.::[scala.Int](3).::[scala.Int](2).::[scala.Int](1));
  x_0.+(1).toDouble
"""
// ^ triple-quotation """ is for multi-line strings

// `Lowering('P)` builds a transformer that inlines all functions marked with phase `P`
// Here we inline `Test.foo`, which is annotated at phase `'MyPhase`
> val pgrm1 = pgrm0 transformWith (new Lowering('MyPhase) with BottomUpTransformer)
pgrm1: ClosedCode[Double] = code"scala.collection.immutable.Nil.::[scala.Int](3).::[scala.Int](2).::[scala.Int](1).head.+(1).toDouble"

// Next, we perform a fixed-point rewriting to partially-evaluate
// the statically-known parts of our program:
> val pgrm2 = pgrm1 fix_rewrite {
    case code"($xs:List[$t]).::($x).head" => x
    case code"(${Const(n)}:Int) + (${Const(m)}:Int)" => Const(n + m)
  }
pgrm2: ClosedCode[Double] = code"2.toDouble"

// Finally, let's runtime-compile and evaluate that program!
> pgrm2.compile
res0: Double = 2.0
```

Naturally, this simple REPL session can be generalized into a proper domain-specific compiler that will work on any input program 
(for example, see the stream fusion compiler [[2]](#gpce17)).

It is then possible to turn this into a static program optimizer,
so that writing the following expression 
expands at compile time into just `println(2)`,
as show in the
[IntroExampleTest](/example/src/test/scala/example/doc/IntroExampleTest.scala#L11)
file:

```scala
MyOptimizer.optimize{ println(Test.foo(1 :: 2 :: 3 :: Nil) + 1) }
```

We could also turn this into a dedicated [Squid macro](#smacros),
an alternative to the current Scala-reflection macros.


## Installation

Squid currently supports Scala versions `2.11.3` to `2.11.11`
(more recent versions might work as well, but have not yet been tested).

The project is not yet published on Maven, 
so in order to use it you'll have to clone this repository
and publish Squid locally,
which can be done by executing the script in `bin/publishLocal.sh`.

In your project, add the following to your `build.sbt`:

```scala
libraryDependencies += "ch.epfl.data" %% "squid" % "0.2.0-SNAPSHOT"
```

Some features related to [library-defined optimizations](#qsr) and [squid macros](#smacros), 
such as `@embed` and `@macroDef`, 
require the use of the [macro-paradise](https://docs.scala-lang.org/overviews/macros/paradise.html)  plugin.
To use these features, add the following to your `build.sbt`:

```scala
val paradiseVersion = "2.1.0"

autoCompilerPlugins := true

addCompilerPlugin("org.scalamacros" % "paradise" % paradiseVersion cross CrossVersion.full)
```


## Overview of Features


### Squid Quasiquotes

Quasiquotes are the primitive tool that Squid provides to manipulate program fragments 
–– building, composing and decomposing them.
Quasiquotes are central to most aspects of program transformation in Squid.

[You can find an in-depth tutorial about Squid quasiquotes here.](/doc/tuto/Quasiquotes.md)

**Note:**
In the original Squid papers [[1]](#scala17) and [[2]](#gpce17),
we used `Code[T]` as the type of program fragments.
With the introduction of scope safety and our POPL paper [[3]](popl18),
this type now takes an extra parameter, as in `Code[T,C]` where `C` represent the term's context requirements.  
We cans still use type `AnyCode[T]` when we don't care about those context requirements; this type has limited capabilities, but can be turned into a proper code type with method `unsafe_asClosedCode`.
On the other hand, `ClosedCode[T]` (a synonym for `Code[T,{}]`) is the type of closed program fragments.


#### Type-Safe Code Manipulation

Unlike the standard [Scala Reflection quasiquotes](https://docs.scala-lang.org/overviews/quasiquotes/intro.html),
Squid quasiquotes are statically-typed and hygienic, 
ensuring that manipulated programs remain well-scoped and well-typed 
and that variable bindings and other symbols do not get mixed up.
Still, Squid quasiquotes support a flexible pattern-matching syntax 
and facilities to traverse programs recursively while applying transformations.


While Squid quasiquotes focus on expressions (not definitions), Squid also provides a way to _embed_ arbitrary class and object definitions so that their methods can be inlined effortlessly, at the discretion of the metaprogrammer.


As a quick reference for Squid users, 
we provide a [cheat sheet](doc/reference/Quasiquotes.md) that summarizes the features of Squid quasiquotes. Also see the [quasiquotes tutorial](/doc/tuto/Quasiquotes.md).



<a name="msp"/>
<a name="qsr"/>

### Multi-Stage Programming and Quoted Staged Rewriting

Squid fully support the multi-staged programming paradigm (MSP), 
allowing the composition and evaluation of program fragments at runtime
(via runtime compilation or reflective interpretation).

In addition, since Squid provides type-safe code inspection capabilities
(a novelty in the field of statically-typed staging),
it can be used to achieve quoted staged rewriting (QSR) [[2]](#gpce17),
an approach to program optimization that mixes the advantages of user-defined rewrite rules, strategic program transformation and MSP.



<a name="ldo"/>

### Library-Defined Optimizations

Squid provides tools to create _static optimizers_, 
which are used to optimize _at compile time_ delimited portions of a user's codebase.
Together with quoted staged rewriting, 
this capability allows for quite flexible and safe library-defined optimizations [[2]](#gpce17).

[Click here to learn more about static optimizers.](doc/Transformers.md#static-optimizers)



<a name="transformers"/>

### Program Transformation Support

Squid supports the definition and composition of custom program transformers and transformation strategies.
This is achieved via Scala mixin-composition and quasiquote-based rewriting declarations.
Squid transformers are type-preserving, 
and they make sure that transformed programs remain well-typed and well-scoped.

[Click here to learn more about Squid transformers.](doc/Transformers.md)


<a name="irs"/>

### Intermediate Representations

Squid quasiquotes, and Squid's infrastructure in general, are unique 
in that they are generic in the actual intermediate representation (IR)
used to encode program fragments.
Custom IRs can be implemented and plugged into Squid to gain the high-level, type-safe features offered by Squid. 
This is done by implementing Squid's object algebra interface [[1]](#scala17).

[Click here to learn more about Squid intermediate representations.](doc/Intermediate_Representations.md)



<a name="smacros"/>

### Squid Macros

Squid macros are an experimental type-safe alternative to legacy scala-reflect macros, based on Squid's infrastructure.
The current implementation is a very rough prototype that should not yet be relied upon.

As an example, here is [the short program transformation](#early-example) 
showed at the beginning of this document,
rewritten as a Squid macro:

```scala
@macroDef(Embedding)
def myMacro(pgrm0: Double) = {
  // in this scope, `pgrm0` has type `Code[Double]`
  val pgrm1 = pgrm0 transformWith (new Lowering('MyPhase) with BottomUpTransformer)
  val pgrm2 = pgrm1 rewrite {
    case code"($xs:List[$t]).::($x).head" => x
    case code"(${Const(n)}:Int) + (${Const(m)}:Int)" => Const(n+m)
  }
  pgrm2
}

// the following should appear in a different project:
myMacro(Test.foo(1 :: 2 :: 3 :: Nil) + 1) // expands into `2.toDouble`
```

(Note: the `macroDef` feature currently lives in experimental branch `squid-macros`.)




## Applications of Squid

Squid is new. See the [examples folder](example/src/main/scala/) for examples. A little query compiler built with Squid can be found [here](https://github.com/epfldata/sc-public/tree/master/relation-dsl-squid). Another LINQ-inspired query engine build with Squid can be found [here](https://github.com/epfldata/dbstage).






## Publications

<a name="scala17">[1]</a>: 
Lionel Parreaux, Amir Shaikhha, and Christoph E. Koch. 2017.
[Squid: Type-Safe, Hygienic, and Reusable Quasiquotes](https://conf.researchr.org/event/scala-2017/scala-2017-papers-squid-type-safe-hygienic-and-reusable-quasiquotes). In Proceedings of the 2017 8th ACM SIGPLAN Symposium on Scala (SCALA 2017).
(Get the paper [here](https://infoscience.epfl.ch/record/231700).)
<!-- https://doi.org/10.1145/3136000.3136005 -->

<a name="gpce17">[2]</a>: 
Lionel Parreaux, Amir Shaikhha, and Christoph E. Koch. 2017.
[Quoted Staged Rewriting: a Practical Approach to Library-Defined Optimizations](https://conf.researchr.org/event/gpce-2017/gpce-2017-gpce-2017-staged-rewriting-a-practical-approach-to-library-defined-optimization).
In Proceedings of the 2017 ACM SIGPLAN International Conference on Generative Programming: Concepts and Experiences (GPCE 2017). Best Paper Award.
(Get the paper [here](https://infoscience.epfl.ch/record/231076).)

<a name="popl18">[3]</a>:
Lionel Parreaux, Antoine Voizard, Amir Shaikhha, and Christoph E. Koch.
[Unifying Analytic and Statically-Typed Quasiquotes](https://popl18.sigplan.org/event/popl-2018-papers-unifying-analytic-and-statically-typed-quasiquotes). To appear in Proc. POPL 2018.
(Get the paper [here](https://infoscience.epfl.ch/record/232427).)


