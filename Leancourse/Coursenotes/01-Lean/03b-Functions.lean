import VersoManual
import Manual.Meta
import Leancourse.Misc.Defs
import Mathlib

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open MyDef

set_option pp.rawOnError true

#doc (Manual) "Function definitions and recursion" =>
%%%
htmlSplit := .never
tag := "function-definitions"
%%%

Having seen Lean's functional style, we now look more closely at how
functions are *defined*: directly, by pattern matching, and by
recursion.

# Function definitions
%%%
tag := "functions"
%%%

In `Lean`, the function `f : ℕ → ℕ, x ↦ 2x` is defined as
```lean
def f : ℕ → ℕ := fun x ↦ 2*x
```
(Write `\mapsto` for `↦`.) It is assumed that the `x` is only introduced to
define `f`. The application of `f` to an `x : ℕ` is then done using `f x`. (The notation `f x` is an abbreviation for `f(x)`, since `Lean` is sparing with parenthesis.)

# Pattern matching
%%%
tag := "pattern-matching"
%%%

For functions on inductive types (like `ℕ`, `List α`, `Option α`,
`Bool`), the most natural way to define them is by *pattern matching*
on the constructors of the input.  The syntax uses `match ... with`
and one branch per constructor, each prefixed by a `|`.

For example, the factorial function on `ℕ` matches on whether the
input is `0` or a successor `n + 1`:

```lean
def factorial : ℕ → ℕ
  | 0     => 1
  | n + 1 => (n + 1) * factorial n
```

Each branch may use the variables introduced by its pattern (here
`n` on the right-hand side).  Lean checks two things automatically:

1. *Exhaustiveness.*  Every constructor of `ℕ` is covered (the cases
   `0` and `n + 1` exhaust `ℕ`).  If you forget a case, Lean
   complains.
2. *Termination.*  The recursive call `factorial n` is on a strictly
   smaller argument than `n + 1`, so the definition is well-founded.

Pattern matching works for any inductive type:

```lean
-- A function on Bool
def negate : Bool → Bool
  | true  => false
  | false => true

-- A function on Option α: extract or use a default
def Option.getD' {α : Type*} (d : α) : Option α → α
  | none   => d
  | some a => a

-- A recursive function on List α
def length' {α : Type*} : List α → ℕ
  | []      => 0
  | _ :: xs => 1 + length' xs
```

The same syntax can be used inline with `match`:

```lean
example (n : ℕ) : ℕ :=
  match n with
  | 0     => 42
  | _ + 1 => 0
```

# Recursion and termination
%%%
tag := "recursion"
%%%

The definitions above are *recursive*: they call themselves on
smaller inputs.  A classic example with two base cases is the
Fibonacci sequence:

```lean
def fib : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | n + 2 => fib n + fib (n + 1)

#eval fib 10    -- outputs 55
```

Lean only accepts a recursive definition once it is convinced the
recursion *terminates*.  For *structural* recursion -- where each
call is on a syntactic sub-part of the input, as in `factorial`,
`length'`, and `fib` -- this is automatic.  When the recursive call
is not on a structural sub-part, you must supply a measure that
decreases, with the `termination_by` and `decreasing_by` clauses;
the underlying theory of *well-founded recursion* is developed in the
Mathematics part.
