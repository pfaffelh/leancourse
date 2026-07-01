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
`length'`, and `fib` -- this is automatic.

When the recursive call is *not* on a structural sub-part, you
justify termination by giving a *measure* that strictly decreases:
the `termination_by` clause names the measure, and `decreasing_by`
discharges the proof that it goes down.  Euclid's algorithm is the
classic example -- `euclidGcd m n` recurses on `n % m`, which is not
a subterm of `m`, but the first argument strictly decreases:

```lean
def euclidGcd (m n : Nat) : Nat :=
  if _h : m = 0 then n
  else euclidGcd (n % m) m
termination_by m
decreasing_by
  exact Nat.mod_lt n (Nat.pos_of_ne_zero _h)

#eval euclidGcd 48 36   -- 12
```

Reading it off: `termination_by m` declares the measure (the first
argument); for the recursive call Lean then asks you to show it
shrinks, i.e. `n % m < m`, which is exactly the goal `decreasing_by`
proves (`Nat.mod_lt` from `m ≠ 0`; the hypothesis `_h` is in scope
thanks to the dependent `if`).  When the decrease is routine,
`decreasing_by` can often close it with `omega`:

```lean
def log2 (n : Nat) : Nat :=
  if _h : 2 ≤ n then 1 + log2 (n / 2) else 0
termination_by n
decreasing_by omega

#eval log2 16   -- 4
```

Under the hood this compiles to *well-founded recursion*
(`WellFounded.fix`); that theory -- what makes a relation
well-founded, and why `<` on `Nat` qualifies -- is developed in the
*Mathematics* part.
