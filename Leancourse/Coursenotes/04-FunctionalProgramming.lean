import VersoManual

import «Leancourse».Coursenotes.«04-FunctionalProgramming».«01-Basics»
import «Leancourse».Coursenotes.«04-FunctionalProgramming».«02-Structures»
import «Leancourse».Coursenotes.«04-FunctionalProgramming».«03-Typeclasses»
import «Leancourse».Coursenotes.«04-FunctionalProgramming».«04-Monads»

open Verso.Genre Manual

#doc (Manual) "Functional Programming" =>
%%%
htmlSplit := .never
tag := "functional-programming"
%%%

Lean is, before anything else, a functional programming language. The
features that make it work as a theorem prover -- inductive types,
dependent types, typeclasses, monads -- all started life as devices for
writing programs.  This part introduces them in their programming guise:

- _Basics_: pure functions, recursion, pattern matching, higher-order
  functions, and the basic inductive types `Nat`, `List`, `Option`.
- _Structures_: bundling several pieces of data into a record-like
  type, and the relationship between `structure` and the more
  permissive `class`.
- _Typeclasses_: how Lean's instance resolution lets you define
  generic operations like `+` once and reuse them across types.
- _Monads_: a uniform way to sequence computations with extra
  structure (failure, state, IO), with `do`-notation as syntactic
  sugar.

Mathlib uses every one of these features at scale; understanding them
makes the rest of the course much easier to read.

{include 0 «Leancourse».Coursenotes.«04-FunctionalProgramming».«01-Basics»}

{include 0 «Leancourse».Coursenotes.«04-FunctionalProgramming».«02-Structures»}

{include 0 «Leancourse».Coursenotes.«04-FunctionalProgramming».«03-Typeclasses»}

{include 0 «Leancourse».Coursenotes.«04-FunctionalProgramming».«04-Monads»}
