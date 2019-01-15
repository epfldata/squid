# Effectful Reification


## Design

I decided _not_ to make `code"..."` quasiquotes themselves effectful (as in, say, LMS, or the old SC backend).
Instead, I use _separate_ functions `.!` and `.bind_!` on coe fragments. The main advantage is that pure programs using
`code"..."` retains the same referentially-transparent meaning, and programs that wish to make use of effectful reification
have to be explicit about it.
It also has the nice property of decoupling effectful reification from the IR being an ANF or similar, where
_every subexpression_ is automatically let-bound by default.


## Typing

Using `.bind_!` produces an `OpenCode` value, because it's not easily possible to track the context of the
automatically-inserted binding. Conceptually, `.bind_!` should return a `Variable[_ <: T]`, but that gives rise to
ugly existential types and unclosable code types anyway.

A possible way to solve this woudl be to use syntax `@reified val x = code{...}`, use the symbol of the `x` binding
itself (similar to what cross-quotation references do), and have a mechanism in the outer QQ to remove such requirements
from the context.


## Syntax

Possible  more lightweight alternatives could be `code{}` and `code_!{}`.
This could probably be done using a different to-level macro which would call calls `wrapEffectfulConstruct` instead of
`wrapConstruct` 

