import VersoManual
import Manual.Meta
import Leancourse.Misc.Defs
import Mathlib

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open MyDef

set_option pp.rawOnError true

#doc (Manual) "Functional Programming Basics" =>
%%%
htmlSplit := .never
tag := "fp-basics"
%%%

Lean is, before anything else, a *functional* programming language.
If you have a background in mathematics but not in programming, do
not worry: functional programming is in many ways closer to
mathematics than imperative programming (like Python or Java).  The
central idea is that programs are built from *functions* in the
mathematical sense -- they take inputs and produce outputs, without
hidden side effects.

Earlier sections in this chapter already introduced the basic
machinery we need: `def` for defining functions, `fun` for anonymous
functions, `inductive` for defining new types, and pattern matching
/ structural recursion for writing functions on inductive types.
The aim of this section is to collect a few extra examples and to
introduce *higher-order functions*, one of the hallmarks of the
functional style.

# Pure functions and `#eval`
%%%
tag := "pure-functions"
%%%

A *pure function* is one whose output depends only on its inputs.
Given the same arguments, it always returns the same result.  This
is exactly how functions work in mathematics: if `f(x) = x + 1`,
then `f(3)` is always `4`.

In Lean, we define functions with `def` and evaluate them with
`#eval`:

```lean
def double (n : ℕ) : ℕ := 2 * n

#eval double 5    -- outputs 10
#eval double 0    -- outputs 0
```

Functions of several arguments are curried: a function of two
arguments is really a function that takes one argument and returns
another function.

```lean
def add (a b : ℕ) : ℕ := a + b

#eval add 3 4    -- outputs 7
```

The type of `add` is `ℕ → ℕ → ℕ`, which reads as `ℕ → (ℕ → ℕ)`.  So
`add 3` is itself a function of type `ℕ → ℕ`.

# Anonymous functions
%%%
tag := "anonymous-functions"
%%%

Sometimes we need a quick, throwaway function without giving it a
name.  We use `fun` (short for "function") with the `↦` arrow
(typed `\mapsto`):

```lean
#eval (fun x : ℕ ↦ x + 1) 5       -- outputs 6
#eval (fun x y : ℕ ↦ x * y) 3 4   -- outputs 12
```

Anonymous functions are particularly useful when passing functions
as arguments to other functions.  In mathematics one would write
`x ↦ x^2`; in Lean we write `fun x ↦ x ^ 2`.

# More examples of recursion
%%%
tag := "fp-more-recursion"
%%%

The `Inductive types` and `Pattern matching` sections above already
covered the fundamentals.  Here are a few further examples that we
will reuse when discussing higher-order functions below.

A binary tree of natural numbers, together with a function that
sums all its values:

```lean
namespace FPBasics

inductive Tree where
  | leaf : Tree
  | node : Tree → ℕ → Tree → Tree

def Tree.sum : Tree → ℕ
  | .leaf => 0
  | .node l v r => Tree.sum l + v + Tree.sum r

#eval Tree.sum
  (.node (.node .leaf 3 .leaf) 5 .leaf)
-- outputs 8

end FPBasics
```

The Fibonacci sequence is a classical example with two base cases:

```lean
def fib : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | n + 2 => fib n + fib (n + 1)

#eval fib 10    -- outputs 55
```

# Higher-order functions
%%%
tag := "higher-order-functions"
%%%

A *higher-order function* is one that takes a function as an
argument or returns a function as a result.  This is one of the
central ideas of functional programming, and it is also very
natural mathematically.  For instance, the derivative is a
higher-order function: it takes a function and returns a function.

The three most important higher-order functions on lists are
`List.map`, `List.filter`, and `List.foldl` (also known as
`fold`).

`List.map` applies a function to every element of a list:

```lean
#eval [1, 2, 3, 4].map (fun x ↦ x * x)
-- outputs [1, 4, 9, 16]
#eval [1, 2, 3].map (· + 10)
-- outputs [11, 12, 13]
```

Note the `·` notation: `(· + 10)` is shorthand for
`(fun x ↦ x + 10)`.

`List.filter` keeps only the elements satisfying a predicate:

```lean
#eval [1, 2, 3, 4, 5, 6].filter
  (fun x ↦ x % 2 == 0)
-- outputs [2, 4, 6]
```

`List.foldl` combines all elements of a list using a binary
operation and an initial value.  It "folds" the list from the left:

```lean
#eval [1, 2, 3, 4].foldl (· + ·) 0
-- outputs 10 (sum)
#eval [1, 2, 3, 4].foldl (· * ·) 1
-- outputs 24 (product)
```

We can define our own higher-order functions.  For example, here is
a function that applies a function `n` times:

```lean
def iterate {α : Type} (f : α → α) : ℕ → α → α
  | 0, x => x
  | n + 1, x => f (iterate f n x)

#eval iterate (· + 1) 5 0        -- outputs 5
#eval iterate (· * 2) 4 1        -- outputs 16
```

We can also write a function that composes two functions:

```lean
def myCompose {α β γ : Type}
    (g : β → γ) (f : α → β) : α → γ :=
  fun x ↦ g (f x)

#eval myCompose (· + 1) (· * 2) 3    -- outputs 7
```

In Lean, function composition is available as `Function.comp` or
simply as `∘` (typed `\circ`).

# Summary
%%%
tag := "fp-basics-summary"
%%%

Functional programming in Lean is built on a few core ideas:

* *Pure functions*: outputs depend only on inputs.
* *Inductive types*: define new types by specifying constructors.
* *Pattern matching*: define functions by cases on the constructors.
* *Structural recursion*: define recursive functions that provably terminate.
* *Higher-order functions*: pass functions as arguments or return them.

These ideas align closely with mathematical practice: inductive
types correspond to inductively defined sets, pattern matching
corresponds to case analysis, and recursion corresponds to
inductive definitions.
