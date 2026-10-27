import VersoSlides
import Verso.Doc.Concrete
import Mathlib

open VersoSlides

set_option pp.rawOnError true

/-
Deck for the chapter "Types and terms I: functions and inductive
types" of part 1 (Lean and its type theory). It follows the chapter
section by section: commands for terms, the universe hierarchy,
function types with their terms, inductive types with pattern
matching and recursion, strict positivity, some history.
-/

namespace SlidesTypes
#doc (Slides) "Types and terms I: functions and inductive types" =>

```css
.reveal section p { font-size: 0.8em; line-height: 1.32; margin: 0.42em 0; }
.reveal section p.key, .reveal section .key p { color: #1b91ff; }
.reveal section table { font-size: 0.62em; margin: 0.2em auto 0.4em; }
.reveal section table th,
.reveal section table td { padding: 0.18em 0.9em; }
.reveal section li { font-size: 0.8em; }
.reveal section .math.display { font-size: 0.7em; }
```

# Types and terms I

Lean and its type theory — chapter 2: functions and inductive types

:::class "key"
In Lean, types can depend on values.
:::

# Every term has a type

`x : α` means: `x` is a term of type `α`.

- `42 : ℕ`, `f : ℕ → ℝ`, `0 ≠ 1 : Prop`
- types may depend on terms: `f : (n : ℕ) → (Fin n → ℝ)`
- `h : P` with `P : Prop` is a _proof_
- `a : α` with `α : Type u` is _data_

:::class "key"
A type is itself a term, so it has a type as well.
:::

# Four steps for every type

:::table +colHeaders +rowSeps
*
  * step
  * question
  * for functions
*
  * formation
  * how is the type written?
  * `α → β`
*
  * construction
  * how is a term built?
  * `fun x => e`
*
  * use
  * how is a term used?
  * `f a`
*
  * computation
  * what happens when a term just built is used?
  * `(fun x => e) a ⟶ e[x := a]`
:::

:::class "key"
Types and terms come together. Chapter 1.4 turns the four steps into rules.
:::

# Commands for terms

```lean -panel -stretch
#check 2 + 2           -- 2 + 2 : ℕ
def four : ℕ := 2 + 2
example : four = 4 := rfl
#eval four             -- 4
```

- `#check t`: the type of `t`
- `def name : T := t`: names `t`; `theorem` for proofs
- `example : T := t`: checks `t`, no name
- `#eval t`: computes the value

# The universe hierarchy

```lean -panel -stretch
#check (ℕ : Type)
#check (Prop : Type)
#check (Type : Type 1)
example : Sort 0 = Prop := rfl
```

`Sort 0` is `Prop`, `Sort (u+1)` is `Type u`. One rule: `Sort u : Sort (u+1)`.

:::class "key"
There is no `Type : Type`: it would give Girard's paradox, a proof of `False`.
:::

# Function types

- _Formation_: `α → β`, or `(x : α) → β x`
- _Construction_: `fun x => e`, also `fun x ↦ e`
- _Use_: application `f a`, no parentheses
- _Computation_: `(fun x => e) a` reduces to `e[x := a]` (β)

```lean -panel -stretch
#check (fun n => n + 1 : ℕ → ℕ)
#eval (fun n : ℕ => n + 1) 4        -- 5
```

# Defining functions

`def name (arguments) : resultType := body` is short for `def name : (arguments) → resultType := fun arguments => body`.

```lean -panel -stretch
def double (n : ℕ) : ℕ := 2 * n
example : double = fun n => 2 * n := rfl

def add (a b : ℕ) : ℕ := a + b
#check add 3     -- add 3 : ℕ → ℕ
```

Functions are _curried_: `ℕ → ℕ → ℕ` is `ℕ → (ℕ → ℕ)`.

# Anonymous functions

```lean -panel -stretch
#eval (fun x : ℕ ↦ x + 1) 5       -- 6
#eval (fun x y : ℕ ↦ x * y) 3 4   -- 12
```

- `↦` is typed `\mapsto`; math `x ↦ x^2` is `fun x ↦ x ^ 2`
- `(· + 10)` is `fun x ↦ x + 10`
- `(· + ·)` is `fun x y ↦ x + y`

# Dependent functions

```lean -panel -stretch
example : ∀ n : ℕ, n < n + 1 :=
  fun n => Nat.lt_succ_self n

def lastOf : (n : ℕ) → Fin (n + 1) :=
  fun n => Fin.last n
#check lastOf 3   -- Fin (3 + 1)
```

:::table +colHeaders
*
  * `β x` is
  * we write
*
  * data
  * `(x : α) → β x`, or `α → β`
*
  * a proposition
  * `∀ x : α, β x`
:::

:::class "key"
`f : (x : α) → β x` picks `f x ∈ β x` for every `x`: an element of $`\prod_x \beta(x)`.
:::

# Polymorphic functions

```lean -panel -stretch
def myId (α : Type) (a : α) : α := a
#check myId ℕ 42          -- ℕ

def myId' {α : Type} (a : α) : α := a
#check myId' 42           -- ℕ, inferred
#check @myId'             -- {α : Type} → α → α

def idStar {α : Type*} (a : α) : α := a
```

:::class "key"
Braces make an argument implicit; `@` shows it again. `Type*`: any universe.
:::

# Proofs as arguments

```lean -panel -stretch
def safeDiv (a b : ℤ) (_ : b ≠ 0) : ℤ := a / b

#eval safeDiv 10 3 (by simp)   -- 3
```

The third argument is a proof of `3 ≠ 0`. Its type depends on `b`, so the type of `safeDiv` is a Π-type.

# Inductive types

```lean -panel -stretch
inductive MyNat where
  | zero : MyNat
  | succ : MyNat → MyNat

example : MyNat := .succ (.succ .zero)
```

- _Formation_: `MyNat : Type`
- _Construction_: the constructors `MyNat.zero`, `MyNat.succ`; `.succ` if the type is known
- _Use_: pattern matching, translated into the recursor `MyNat.rec`
- _Computation_: a match on a constructor takes its branch (ι)

# More inductive types

```lean -panel -stretch
inductive Colour where
  | red | green | blue

inductive MyOption (α : Type) where
  | none : MyOption α
  | some : α → MyOption α

example : MyOption ℕ := .some 3
```

`MyOption α` is a type for every type `α`.

# Pattern matching

One branch per constructor, each prefixed by `|`.

```lean -panel -stretch
def factorial : ℕ → ℕ
  | 0     => 1
  | n + 1 => (n + 1) * factorial n
```

Lean checks automatically:

- _exhaustiveness_: every constructor is covered,
- _termination_: `factorial n` is on a smaller argument.

# Matching on your own types

```lean -panel -stretch
def MyNat.double : MyNat → MyNat
  | .zero   => .zero
  | .succ n => .succ (.succ (MyNat.double n))

def MyNat.toNat : MyNat → ℕ
  | .zero   => 0
  | .succ n => MyNat.toNat n + 1

#eval (MyNat.double (.succ .zero)).toNat   -- 2
```

`m.toNat` means `MyNat.toNat m`.

# Any inductive type

`List α`: constructors `[]` and `a :: l`. The pattern `_` matches anything.

```lean -panel -stretch
def length' {α : Type*} : List α → ℕ
  | []      => 0
  | _ :: xs => 1 + length' xs

example (n : ℕ) : ℕ :=
  match n with
  | 0     => 42
  | _ + 1 => 0
```

# Recursion

```lean -panel -stretch
def fib : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | n + 2 => fib n + fib (n + 1)

#eval fib 10    -- 55
```

Lean accepts recursion only once it sees that it terminates.

:::class "key"
Structural recursion, calls on parts of the input, is automatic.
:::

# Termination by a measure

`termination_by` names a measure, `decreasing_by` proves it drops.

```lean -panel -stretch
def euclidGcd (m n : Nat) : Nat :=
  if _h : m = 0 then n
  else euclidGcd (n % m) m
termination_by m
decreasing_by
  exact Nat.mod_lt n (Nat.pos_of_ne_zero _h)
```

Goal: `n % m < m`. The dependent `if` puts `_h : m ≠ 0` in scope. Routine cases: `decreasing_by omega`.

# Proving things about recursive definitions

```lean -panel -stretch
def log2 (n : Nat) : Nat :=
  if _h : 2 ≤ n then 1 + log2 (n / 2) else 0

example (n : ℕ) : fib (n + 2) = fib n + fib (n + 1) :=
  rfl
example : log2 16 = 4 := by simp [log2]
```

Structural recursion computes, so `rfl` works. Well-founded recursion does not: use the equation lemma `log2.eq_1`, via `rw [log2]`, `unfold log2` or `simp [log2]`.

# The recursor

```lean -panel -stretch
#check @MyNat.rec
```

`motive : MyNat → Sort u` is the type of the result, depending on the input.

:::class "key"
Data-valued motive: recursion. `Prop`-valued motive: induction.
:::

# Strict positivity

```lean -panel -stretch
inductive MyTree where
  | leaf : ℕ → MyTree
  | node : (ℕ → MyTree) → MyTree
```

```
inductive Bad where
  | mk : (Bad → False) → Bad   -- rejected
```

The argument of `node` has type `ℕ → MyTree`: `MyTree` right of `→`. The argument of `Bad.mk` has type `Bad → False`: `Bad` left of `→`. With `Bad`, `neg b := app b b` gives `neg (Bad.mk neg) : False`.

:::class "key"
In the argument types of a constructor, the type may occur only to the right of an arrow.
:::

# Some history

Russell's set $`R = \{x : x \notin x\}` broke Frege in 1902. Russell's repair (1908): `x ∈ x` is not a statement at all.

:::table +colHeaders +rowSeps
*
  * system
  * broken by
  * repaired by
*
  * Frege, _Grundgesetze_
  * Russell, 1902
  * types, 1908
*
  * Church's lambda calculus, 1932
  * Kleene, Rosser, 1935
  * simple types, 1940
*
  * Martin-Löf, 1971
  * Girard
  * universe hierarchy
:::

Then the Calculus of Constructions (1985) and inductive types (1990).

# Summary

- Universes: `Prop`, `Type 0 : Type 1 : ...`; there is no `Type : Type`.
- Functions: `(x : α) → β x`, built with `fun`, used by application, computed by β.
- `def`, currying, `fun x ↦ …`, `·`, implicit and universe-polymorphic arguments.
- `inductive`: built with constructors, used by pattern matching, computed by ι.
- Recursion must terminate; constructors must be strictly positive.
