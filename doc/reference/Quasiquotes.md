# Quasiquotes Cheat Sheet


## Intermediate Representation Base

In order to manipulate code fragments, one has to chose an intermediate representation (IR) in which these are to be encoded. (For more details, see the [documentation about IRs](/doc/Intermediate_Representations.md).)

Once an IR is created and named (for example) `Embedding`, the use of quasiquotes and related features is enabled by importing `Embedding.Predef._`.
The use of quasicode (presented below) is enabled by importing `Embedding.Quasicode._`.

For example:

```scala
object Embedding extends squid.ir.SimpleAST

import Embedding.Predef._
println(code"123.toDouble")  // quasiquote

import Embedding.Quasicodes._
println(code{123.toDouble})  // quasicode
```



## Quasiquotes

**Quasiquotes [(see the tutorial here)](/doc/tuto/Quasiquotes.md)** 
are written `code"..."` (or with short syntax `c"..."`),
and have type `Code[T,C]`
where type argument `T` reflects the type of the term (program fragment) represented by the quasiquote,
and `C` reflects the _context requirements_ of that term.


## Related Code Types

Sometimes, you may not care about the context of a program fragment,
in which case you can use the type `AnyCode[T]`,
since we have the subtyping relation `Code[T,C] <: AnyCode[T]`.
On the other hand,
any term of type `AnyCode[T]`,
can be _casted_ (converted) into a contextual term with the unsafe method `.unsafe_asClosedCode` 
–– this cast is only well-defined if the simple term does not have free variables (i.e., it is a _closed_ term).
This conversion returns a `ClosedCode[T]`, 
which is itself a type alias for `Code[T,Any]` (a piece of code valid in **any** context).
We will sometimes write `Code[T,{}]` for aesthetic reasons, 
leveraging the fact that since `{} == AnyRef <: Any`, we have `Code[T,Any] <: Code[T,{}]`, 
but in general using type `Code[T,Any]` (or equivalently, `ClosedType[T]`) 
works slightly better with type inference.



## Quasicode

An alternative to quasiquotes, **quasicode** is 
written `code{...}`.
Quasicoding has the following limitations compared to quasiquotation:
 
 * cannot be used in patterns (due to a Scala limitation);
 
 * cannot use the short `$x` unquotation syntax and have to use `${x}` instead (or, alternatively, `$(x)`);
 
 * cannot directly insert type representations: if I have `t: CodeType[T]`, 
 I can write `code"List.empty[$t]"`
 but I cannot write `code{List.empty[${t}]}`
 –– this is not an important limitation in practice, as one can always write 
 either `code{List.empty[T]}` or `code{List.empty[t.Typ]}` instead.
 
 * cannot benefit from GADT-like type coercion (see the [relevant section](#gadt-coercion) of this document).
 


## Basic Features of Quasiquotes

All other features available to quasiquotes are also available to quasicode, so in the following, examples that uses syntax `code"..."` can usually be translated to the alternative `code{...}` syntax.


### Supported Scala Features

Squid quasiquotes are for manipulating **expressions**
–– meaning that **definitions** (of classes, traits, objects, methods and types)
cannot appear inside quasiquotes, though _references_ to such externally-defined constructs can.
If you want to manipulate definitions, other tools exist (for example, see [Scalameta](http://scalameta.org/)). These tools typically have much weaker guarantees
–– indeed, by its very nature, manipulating definitions cannot usually be type-preserving and type-safe 
(e.g., changing the fields of a class will likely break programs that used the old field definitions).


Currently supported term-level features of quasiquotes:
 
 * constant literals
 for types `Unit`, `Boolean`, `Byte`, `Char`, `Short`, `Int`, `Long`, `Float`, `Double`, `String` and `Class[_]` for class references (such as `classOf[List[_]]`; these arise as part of the inferred type tags passed to array constructors, for example);
 
 * value (`val`) and variable (`var`) bindings –– note that we do not support `lazy val` yet;
 
 * lambda abstractions of arity 0 to 22 (though some IRs may have additional ad-hoc restrictions to the highest supported arity);
 
 * by-name arguments;
 
 * variadic arguments and variadic argument splices with `:_*`;
 
 * object (a.k.a. module) references: both static (as in `scala.Predef`) and rooted in runtime values (as in `List.canBuildFrom`);
 
 * field accesses;
 
 * method calls with arbitrary numbers of type parameters and value parameter lists;
 
 * instantiation with keyword `new`;
 
 * imperative effects (as in `code"println(123); ..."`);
 
 * if-then-else conditional branches;
 
 * while loops;
 
 * type ascription (syntax `someTerm: SomeType`).
 
 
Scala features that desugar into supported features (non-exhaustive list):
 
 * for loops/monadic comprehensions: desugar into method applications;
 
 * implicit arguments: desugar into normal arguments;
 
 * named arguments in method calls: desugar into value bindings and normal method calls;
 
 * tuples: desugar into `TupleN` objects and types;
 
 * package objects: these are simply objects named `` `package` ``;
 
 * nested quasiquotes: it is possible to nest quasiquotes and quasicode,
   as in `ir""" ir"List(1,2,3).map(_+1)" """` and `ir{ir{List(1,2,3).map(_+1)}}` respectively, since the inner quasiquote expands first (during the time it is type-checked), resulting in code that can be embedded by the outer quasiquote;
   there are currently some limitations with nesting contextual quasiquotes that represent open terms, as that would generate structural type refinements, currently not supported by Squid (see below).
 


Scala features that will probably be supported in the future:

 * [pattern matching](https://github.com/epfldata/squid/issues/26): will be converted into a virtualized form;
 
 * variable references that cross quotation boundaries:
   with syntax `code{(x:Int) => ${ foo(code{x + 1}) }}` for quasicode 
   and or `code"(x:Int) => ${ foo(code"$$x + 1") }"` for quasiquotes;
 
 * lazy values –– these are easy to virtualize.
 

Currently supported type-level features:

[TODO]


Feature not likely to be supported in the future (unless a strong need emerges):
 
 * definitions in general (classes, traits, objects, types, methods): 
   in particular, one problem is that methods can be polymorphic but Squid currently relies on monomorphic code representation (although such code representations can be manipulated in polymorphic ways!);
 
 * existential types;
 
 * path-dependent types;
 
 * structural type refinements;
 
 * higher-kinded types: note that using type aliases may circumvent this limitation (for example, `code"List.canBuildFrom[Int]"` works and has type `Code[collection.generic.CanBuildFrom[List.Coll, Int, List[Int]]]` because type alias `List.Coll` is not expanded);
 
 * `new` syntax with refinement: because this is analogous to defining a local class.

Note that when a Squid quasiquote cannot represent a type, 
it may fall back to calling an `uninterpretedType` method for some of these cases,
where the IR is then free to carry around the type captured as a Scala reflection `TypeTag`. However, matching against and extracting sub-types from such types will not be supported by Squid quasiquotes.




### Term Composition and Decomposition

Quasiquotes can be used in both expressions and patterns.
The unquote syntax, written `${xyz}` or just `$xyz` if `xyz` is an identifier, 
has different meanings depending on whether we are in expression or pattern mode:
 
 * In expressions, unquotes _insert_ into the enclosing code fragment, at the place of the unquote, whatever terms are unquoted;
 for example, `c"Some(${ c"123.toDouble" })" == c"Some(123.toDouble)"`;
 
 * In patterns, unquotes _extract_ code that is found in the current enclosing fragment, at the place of the unquote, and match it with the pattern present in the unquote;
 for example, `c"Some(123.toDouble)" match {case c"Some(($n:Int).toDouble)" => n} == c"123"`.



### Constants

Constants can be constructed and deconstructed with syntax `Const(value)`.
For example:

```scala
val q0 = code"println(123)" match { 
  case c"println(${Const(n)}:Int)" => c"println(${Const(n+1)})" }
assert(q0 == code"println(124)")
```




### Variadic Arguments (Varargs) and Splicing

In expressions and patterns, special "unquote-splicing" syntax `${xyz}*`
(or `$xyz*` if `xyz` is an identifier)
will insert and extract sequences of code types (`Seq[Code[Int]]`).

For example:

```scala
val q0 = code"Seq(1,2,3)" match {
  case code"Seq[Int]($xs*)" =>
    // xs: Seq[ClosedCode[Int]]
    assert(xs == Seq(c"1",c"2",c"3"))
    val xs2 = c"0" +: xs
    code"Seq[Int](${xs2}*)"
    // a current limitation/bug prevents the following syntax:
    // code"Seq[Int](${c"0" +: xs}*)"
}
assert(q0 == code"Seq(0,1,2,3)")
```

Note that alternative syntaxes for this exist: 
in expressions, one can write `c"Seq[Int](${xs: _*})"`
and in pattern, one can write `c"Seq[Int](${xs @ __*})"`.


Unquote-splicing is not to be confused with the Scala `_*` syntax, which is supported normally inside quasiquotes. Writing `$xs:_*` implies that `xs` has type `ClosedCode[Seq[Int]]`, _not_ `Seq[Code[Int]]`. For example:

```scala
def mkSeq(n: Int): Seq[Int] = ???
code"List(mkSeq(3): _*)" match {
  case code"List[Int]($xs: _*)" =>
    assert(xs == c"mkSeq(3)")
}
```


### Type Extraction

Not only terms can be extracted by quasiquotes patterns, but also types.
This yield type representation values `t` of type `CodeType[t.Typ]`.
For example:

```scala
def opt(x: AnyCode[Any]) = x match {
  case code"List[$t]($xs*).size" => Const(xs.size)
  case _ => x
}
assert(opt(c"List(1,2).size") == c"2")
```


### Escaped Unquote Syntax

It is possible to _insert_ code into _patterns_ by escaping the `$` sign, as follows:

```scala
val x = code"42"
code"Seq(42)" match {  // or:  code"Seq($x)" match { ...
  case code"Seq($$x)" => // this matches
}
```

Another example, featuring type escaped unquote for a type representation:

```scala
val x = c"List(1,2)"
val y = c"List(2,3)"
val z = c"List(true,false)"
x match {
  case code"List[$t]($a,$b)" =>
  // ^ extracts `t == Int; a == 1; b == 2`
    y match {
      case code"List[$$t]($c,$d)" => // matches
    }
    z match {
      case code"List[$$t]($c,$d)" => assert(false)
      // ^ does not match, since `Int != Bool`
      case _ =>
    }
}
```



### Repeated Holes

Pattern holes (unquotes) can be used several times in a single pattern.
However, due to a Scala limitation, only (an arbitrary) one of the hole's occurrences should be mark with a `$` sign. For example:

```scala
val x = c"List(1,2)"
val y = c"List(2,1)"
code"$x -> $y" match {
  case code"List[$t]($a,a) -> List[$s]($b,b)" => assert(false) // doesn't match
  case code"List[$t]($a,b) -> List[t]($b,a)" => // matches
  // ^ notice we repeat holes `t`, `a` and `b`
}
```

<!-- order does not matter -->







### Implicit Type Evidence Manipulation

TODO



<a name="gadt-coercion"/>

### GADT-like Type Refinement in Pattern Matching Branches

TODO






### Miscellaneous

TODO






## More Advanced, Contextual Features of Quasiquotes

TODO

### Substitution, Renaming

### Open Terms

### Free variables

```scala
code"(?x: String).length"
```

they can be achieved anyway with something like:
```scala
//  open: Q[Int, {x: String}]
val open = code"(x: String) => x.length" match {
  case code"(x => $body: String)" => body
}
```

### References to Enclosing `this`







