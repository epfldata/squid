# **Squid** ― Scala Quoted DSLs

[![Join the chat at https://gitter.im/epfldata-squid/Lobby](https://badges.gitter.im/epfldata-squid/Lobby.svg)](https://gitter.im/epfldata-squid/Lobby?utm_source=badge&utm_medium=badge&utm_campaign=pr-badge&utm_content=badge)



## Introduction

**Squid** (for the approximative contraction of **Sc**ala **Qu**ot**ed** **D**SLs)
is a **metaprogramming** framework 
that facilitates the **type-safe** manipulation of **Scala programs**.
Squid is geared towards
the implementation of **library-defined optimizations** [[2]](#gpce17) and 
helps with the compilation of **Domain-Specific Languages** (DSL) embedded in Scala [[1]](#scala17).
In addition, it has an advanced static typing capabilities that reduce common metaprogramming errors [[3]](#popl18).

<!-- TODO: give concrete application examples to pique curiosity/generate interest -->

**Caution:** Squid is still experimental, and the interfaces it exposes may change in the future (especially the semi-internal interfaces used to implement intermediate representation backends).


## Installation

Squid currently supports Scala versions `2.11.3` to `2.11.11`
(more recent versions might work as well, but have not yet been tested).

The project is not yet published on Maven, 
so in order to use it you'll have to clone this repository
and publish Squid locally,
which can be done by executing the script in `bin/publishLocal.sh`.

In your project, add the following to your `build.sbt`:

```scala
libraryDependencies += "ch.epfl.data" %% "squid" % "0.2-SNAPSHOT"
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


#### Type-Safe Code Manipulation

Unlike the standard [Scala Reflection quasiquotes](https://docs.scala-lang.org/overviews/quasiquotes/intro.html),
Squid quasiquotes are statically-typed and hygienic, 
ensuring that manipulated programs remain well-typed 
and that variable bindings and other symbols do not get mixed up.
Squid quasiquotes focus on expressions (not definitions), but Squid provides way to _embed_ arbitrary class and object definitions so that their methods can be inlined at any point (or even automatically).


#### Flavors of Quasiquotes

Two forms of quasiquotes co-exist in Squid:

 * **Simple Quasiquotes [(tutorial)](/doc/tuto/Quasiquotes.md)** provide the basic functionalities expected from statically-typed quasiquotes,
   and can be used for a wide range of tasks, including [multi-stage programming (MSP)](https://en.wikipedia.org/wiki/Multi-stage_programming).
   They support both runtime interpretation, runtime compilation and static code generation.
   For more information, see [[1]](#scala17).

 * **Contextual Quasiquotes [(tutorial)](/doc/tuto/Quasiquotes.md)** 
   push the type-safety guarantees already offered by simple quasiquotes even further,
   making sure that all generated programs are well-scoped in addition to being well-typed.
   While they are slightly less ergonomic than the previous flavor, 
   these quasiquotes are especially well-suited for expressing advanced program transformation algorithms and complicated staging techniques.
   For more information, see [[3]](#popl18).

Both forms of quasiquotes support a flexible pattern-matching syntax 
and facilities to traverse programs recursively while applying transformations.

As a quick reference available to all Squid users, 
we provide a [cheat sheet](doc/reference/Quasiquotes.md) that summarizes the features of each system. Also see the [quasiquotes tutorial](/doc/tuto/Quasiquotes.md).



<a name="transformers"/>

### Program Transformation Support

TODO

[Link to transformers documentation](doc/Transformers.md).


<a name="irs"/>

### Intermediate Representations

TODO

[Link to IR documentation](doc/Intermediate_Representations.md)


<a name="qsr"/>

### Library-Defined Optimizations with Quoted Staged Rewriting (QSR)

TODO



<a name="smacros"/>

### Squid Macros

TODO




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
Unifying Analytic and Statically-Typed Quasiquotes. To appear in Proc. POPL 2018.


