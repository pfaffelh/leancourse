import VersoSlides
import Verso.Doc.Concrete
import Mathlib

open VersoSlides

set_option pp.rawOnError true

/-
Deck for the chapter "Types and terms I: functions and inductive
types" of part 1 (Lean and its type theory). It follows the chapter
section by section: commands for terms, the universe hierarchy,
function types with their terms, structures, inductive types with pattern
matching and recursion, strict positivity, some history.
-/

namespace SlidesTypes
#doc (Slides) "Types and terms I: functions, structures, inductive types" =>

```css
.reveal section p { font-size: 0.8em; line-height: 1.32; margin: 0.42em 0; }
.reveal section p.key, .reveal section .key p { color: #1b91ff; }
.reveal section table { font-size: 0.62em; margin: 0.2em auto 0.4em; }
.reveal section table th,
.reveal section table td { padding: 0.18em 0.9em; }
.reveal section li { font-size: 0.8em; }
.reveal section .math.display { font-size: 0.7em; }
.reveal section .small table, .reveal section table.small { font-size: 0.52em; }
.reveal section .small td, .reveal section table.small td { padding: 0.1em 0.8em; }
```

# Types and terms I

Lean and its type theory — chapter 2: functions, structures, inductive types

:::class "key"
In Lean, types can depend on values.
:::

# Every term has a type

`x : α` means: `x` is a term of type `α`.

- `42 : ℕ`, `f : ℕ → ℝ`, `0 ≠ 1 : Prop`
- propositions may depend on terms: `∀ n : ℕ, n < n + 1 : Prop`
- types may depend on terms: `f : (n : ℕ) → (Fin n → ℝ)`, so `f n` is a vector in $`\mathbb{R}^n`
- `Fin n`: the numbers `i < n`; an element is a pair `⟨i, h⟩` with `h : i < n`
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
theorem four_eq : four = 4 := rfl
example : four = 4 := rfl
#eval four             -- 4
```

- `#check t`: the type of `t`
- `def name : T := t`: names `t`
- `theorem name : P := p`: names a proof; Mathlib also accepts `lemma`
- `example : T := t`: checks `t`, no name
- `#eval t`: computes the value

# The universe hierarchy

:::table +colHeaders +rowSeps
*
  * universe
  * its terms, for example
  * lives in
*
  * `Prop` = `Sort 0`
  * `2 = 2`, `∀ n : ℕ, n < n + 1`
  * `Type`
*
  * `Type` = `Type 0` = `Sort 1`
  * `ℕ`, `ℝ`, `Bool`, `ℕ → ℝ`, `Prop`
  * `Type 1`
*
  * `Type 1` = `Sort 2`
  * `Type`, `ℕ → Type`
  * `Type 2`
*
  * `Type u` = `Sort (u + 1)`
  * …
  * `Type (u + 1)`
:::

:::class "key"
One rule: `Sort u : Sort (u + 1)`. So `Prop : Type`.
:::

`{α : Type*}` in a signature: `α` lies in some universe `Type u`, and Lean introduces the variable `u` itself.

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

#eval safeDiv 10 3 (by decide)   -- 3
```

The third argument is a proof of `3 ≠ 0`; `decide` finds it by computing. Its type depends on `b`, so the type of `safeDiv` is a Π-type.

# Structures

```lean -panel -stretch
structure Point where
  x : ℕ
  y : ℕ

example : (Point.mk 3 4).x = 3 := rfl
example (p : Point) : p = Point.mk p.x p.y := rfl
```

- _Formation_: `Point : Type`
- _Construction_: the one constructor `Point.mk`
- _Use_: projections `Point.x p`, written `p.x`
- _Computation_: `(Point.mk 3 4).x` reduces to `3`; η: `p ≡ Point.mk p.x p.y`

# Building values

```lean -panel -stretch
def p1 : Point := ⟨1, 2⟩
def p2 : Point := { x := 3, y := 4 }
def p3 : Point where
  x := 0
  y := 0
def p4 : Point := { p1 with y := 10 }
```

Anonymous constructor, record, `where` form: all call `Point.mk`.

:::class "key"
Structures are immutable: `with` builds a new `Point`.
:::

# Defaults and extensions

```lean -panel -stretch
structure MyConfig where
  width : ℕ := 80
  title : String := "Untitled"
def myConfig : MyConfig := { title := "Win" }

structure Point3D extends Point where
  z : ℕ
def q : Point3D := { x := 1, y := 2, z := 3 }
#eval q.x    -- 1 (inherited)
```

# Data with a property

```lean -panel -stretch
structure IntAddMap where
  toFun : ℤ → ℤ
  map_add : ∀ x y,
    toFun (x + y) = toFun x + toFun y

def triple : IntAddMap where
  toFun x := 3 * x
  map_add x y := mul_add 3 x y
```

:::class "key"
A field may be a proof. Linear maps, continuous functions, homomorphisms: all of this kind.
:::

# `Fin n` and `∧` are structures

```lean -panel -stretch
#check @Fin.mk
example : Fin 3 := ⟨2, by decide⟩

example (P Q : Prop) (h : P ∧ Q) : Q ∧ P :=
  ⟨h.2, h.1⟩
```

- `Fin n`: a number `val` and a proof `isLt : val < n`
- `P ∧ Q`: two proofs, fields `left` and `right`; `h.1`, `h.2`

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

# Disjunction is an inductive type

```lean -panel -stretch
inductive MyOr (a b : Prop) : Prop where
  | inl : a → MyOr a b
  | inr : b → MyOr a b

example (P Q : Prop) (hP : P) : MyOr P Q := .inl hP
```

Two constructors: a proof of `P ∨ Q` is a proof of `P` or one of `Q`, marked by the constructor. Lean's `∨` is `Or`, declared in this way.

# Structures and inductive types

::::class "small"
:::table +colHeaders +rowSeps
*
  * constructors
  * data
  * proposition
*
  * none
  * `Empty`
  * `False`
*
  * one, no arguments
  * `Unit`
  * `True`
*
  * two, no arguments
  * `Bool`
  * —
*
  * one, two arguments
  * `α × β`
  * `P ∧ Q`
*
  * two, one argument each
  * `α ⊕ β`
  * `P ∨ Q`
*
  * one, value and proof
  * `{x : α // P x}`
  * `∃ x, P x`
*
  * recursive
  * `ℕ`, `List α`
  * `n ≤ m`
:::
::::

:::class "key"
A `structure` is an inductive type with one constructor, plus field names, projections, defaults and `extends`.
:::

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

# Or with the recursor

```lean -panel -stretch
noncomputable def MyNat.double' (n : MyNat) :
    MyNat :=
  MyNat.rec .zero (fun _ d => .succ (.succ d)) n

example : MyNat.double' (.succ .zero) =
    .succ (.succ .zero) := rfl
```

As with `Nat.rec` in 1.1: one argument per constructor. Lean's compiler does not run the recursor of your own type, hence `noncomputable`: `rfl` works, `#eval` does not.

:::class "key"
Pattern matching is translated into the recursor for the kernel, and into running code for `#eval`.
:::

# Lists

```
inductive List (α : Type u) where
  | nil : List α                    -- written []
  | cons (a : α) (l : List α) :
      List α                        -- written a :: l
```

```lean -panel -stretch
#eval (1 :: 2 :: 3 :: [] : List ℕ)   -- [1, 2, 3]
```

A list is empty, or a first element followed by a list. `[1, 2, 3]` is notation for `1 :: 2 :: 3 :: []`.

# Functions on lists

One branch per constructor; the pattern `_` matches anything. `match` does the same inside a term.

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

example : fib 3 = 2 := rfl
```

- `fib (n + 2)` calls `fib n` and `fib (n + 1)`: smaller arguments. This is *structural recursion*.
- Lean checks this and translates `fib` into the recursor `Nat.rec` of 1.1. So `fib` computes by ι:
  `fib 3 ⟶ fib 1 + fib 2 ⟶ 1 + (fib 0 + fib 1) ⟶ 1 + (0 + 1)`.
- `def bad (n : ℕ) : ℕ := bad n + 1` is rejected. It would give `bad 0 = bad 0 + 1`, so `0 = 1`.

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

Curry (1934), Howard (1969): propositions are types, proofs are terms. Then the Calculus of Constructions (1985) and inductive types (1990).

# Summary

- Universes: `Prop`, `Type 0 : Type 1 : ...`; there is no `Type : Type`.
- Functions: `(x : α) → β x`, built with `fun`, used by application, computed by β.
- `def`, currying, `fun x ↦ …`, `·`, implicit and universe-polymorphic arguments.
- `structure`: one constructor, named fields, projections; a field may be a proof. `Fin n` and `∧` are structures.
- `inductive`: built with constructors, used by pattern matching, computed by ι. `∨` is one of them.
- Recursion must terminate. Structural recursion becomes the recursor; well-founded recursion is used through its equation lemmas.
- Constructors must be strictly positive.
