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

# Exploring definitions with `#check`, `#print` and `inferInstance`
%%%
tag := "checkprint"
%%%

We have already been using `#eval` to run our functions.  Lean
provides a handful more *commands* that are invaluable for exploring a
library like Mathlib.  They all start with `#` and only print
information -- they do not contribute to a proof.

- `#check e` prints the type of the term or expression `e`.  This is
  the fastest way to learn what a lemma says, or what type a definition
  has.
- `#check @lemma` (with a leading `@`) prints the type of the lemma
  *without* hiding implicit and instance arguments.  Use `@` when you
  want to see every argument.
- `#print name` prints the *definition* of the constant `name`.  For a
  typeclass, this shows you the list of fields; for a `def`, the body;
  for a `structure`, the constructor and fields.
- `#eval e` evaluates the term `e` (when it is computable) and prints
  the result.  It works on concrete `ℕ`, `List`, etc., but not on
  abstract propositions.

A very common idiom is to ask Lean whether a given type has a specific
instance (e.g. "is `ℕ` a commutative monoid?"):

```lean
-- "Does ℕ have an AddCommMonoid instance?" -- yes.
#check (inferInstance : AddCommMonoid ℕ)
```

The term `inferInstance` asks Lean to synthesize an instance of the
indicated type; if no such instance exists the command will fail with
a readable error message.

Two tactics complement these commands during an interactive proof:

- `exact?` searches Mathlib for a single lemma that closes the current
  goal and prints a `exact <lemma>` line you can copy.
- `apply?` is the same, but it suggests lemmas whose *conclusion*
  matches the goal, leaving side conditions as new subgoals.

Together, `#check`, `#print`, `inferInstance`, `exact?` and `apply?`
are the main tools for navigating an unfamiliar part of Mathlib; for
searching the library by content or name, see
{ref "navigating-mathlib"}[Navigating Mathlib] in the appendix.
