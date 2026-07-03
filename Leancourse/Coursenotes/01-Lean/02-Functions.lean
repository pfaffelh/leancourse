import VersoManual
import Manual.Meta
import Leancourse.Misc.Defs
import Mathlib

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open MyDef

set_option pp.rawOnError true

#doc (Manual) "Functions" =>
%%%
htmlSplit := .never
tag := "functions"
%%%

Lean is, before anything else, a *functional* programming language --
it essentially consists only of functions.  This paradigm contrasts
with *imperative* languages such as Python, Java, or C.  If you have
a background in mathematics but not in programming, do not worry:
functional programming is in many ways closer to mathematics than
imperative programming -- programs are built from *functions* in the
mathematical sense, taking inputs to outputs without hidden side
effects.

# Defining and evaluating functions
%%%
tag := "pure-functions"
%%%

We define functions with `def` and evaluate them with `#eval`.
Recall (previous chapter) that `x : α` means "`x` is a term of type
`α`".  A definition has the shape

```
def name (arguments) : resultType := body
```

so the following defines `double`, taking one argument `n : ℕ` and
returning the `ℕ` value `2 * n`:

```lean
def double (n : ℕ) : ℕ := 2 * n

#eval double 5    -- outputs 10
#eval double 0    -- outputs 0
```

Application is written `f x` (no parentheses -- `f x` is Lean's way
of writing `f(x)`).  A *pure function* returns the same result for
the same arguments, exactly as in mathematics.

Functions of several arguments are *curried*: a function of two
arguments is really a function that takes one argument and returns
another function.

```lean
def add (a b : ℕ) : ℕ := a + b

#eval add 3 4    -- outputs 7
```

The type of `add` is `ℕ → ℕ → ℕ`, which reads as `ℕ → (ℕ → ℕ)`; so
`add 3` is itself a function of type `ℕ → ℕ`.

# Polymorphic functions
%%%
tag := "polymorphic-functions"
%%%

Functions can take *types* as arguments, not just values -- this is how
you write a single definition that works for every type.  The identity
function is the basic example:

```lean
def myId (α : Type) (a : α) : α := a
#check myId ℕ 42        -- ℕ
```

Usually you do not want to pass the type explicitly every time, so you
make it an *implicit* argument with braces `{...}`; Lean then infers it
from the value:

```lean
def myId' {α : Type} (a : α) : α := a
#check myId' 42         -- ℕ, inferred
```

A definition that should also work at *any universe level* -- recall
the {ref "type-universes"}[universe hierarchy] -- uses a universe
variable.  You may introduce one with the `universe` command, or, most
commonly, write `Type*`, which inserts a fresh universe variable for
you:

```lean
universe u
def idOne (α : Type u) (a : α) : α := a

def idStar {α : Type*} (a : α) : α := a
```

This is why signatures throughout Mathlib read `{α : Type*}`: the same
definition then applies whether `α` is small like `ℕ` or large like
`Type` itself.  We use `{α : Type*}` freely in the examples below.

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

In mathematics one would write `x ↦ x^2`; in Lean we write
`fun x ↦ x ^ 2`.  There is an even shorter form using the `·`
placeholder (a centered dot, typed `\cdot`): a `·` stands for an
anonymous argument, so `(· + 10)` is shorthand for `fun x ↦ x + 10`,
and several `·` become successive arguments -- `(· + ·)` means
`fun x y ↦ x + y`.

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
