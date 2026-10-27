import VersoSlides
import Verso.Doc.Concrete
import Mathlib

open VersoSlides

set_option pp.rawOnError true

/-
Deck for the chapter "Types II: type formers" of part 1 (Lean and its
type theory). It follows the chapter section by section: function
types and Π-types, inductive types, structures, Σ-types, subtypes,
type families, quotient types.
-/

namespace SlidesTypeFormers
#doc (Slides) "Types II: type formers" =>

```css
.reveal section p { font-size: 0.8em; line-height: 1.32; margin: 0.42em 0; }
.reveal section p.key, .reveal section .key p { color: #1b91ff; }
.reveal section table { font-size: 0.62em; margin: 0.2em auto 0.4em; }
.reveal section table th,
.reveal section table td { padding: 0.18em 0.9em; }
.reveal section li { font-size: 0.8em; }
.reveal section .math.display { font-size: 0.7em; }
```

# Types II: type formers

Lean and its type theory — chapter 3

:::class "key"
In Lean, types can depend on values.
:::

# Function types and Π-types

```lean -panel -stretch
#check (fun n => n + 1 : ℕ → ℕ)

example : ∀ n : ℕ, n < n + 1 :=
  fun n => Nat.lt_succ_self n
```

Both are instances of `(x : α) → β x`; here `β n` is `n < n + 1`, which depends on `n`.

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

# Dependent functions

```lean -panel -stretch
def lastOf : (n : ℕ) → Fin (n + 1) :=
  fun n => Fin.last n
#check lastOf 3   -- Fin (3 + 1)

def polyId : (α : Type) → α → α :=
  fun _ a => a
#check polyId ℕ 42  -- ℕ
```

:::class "key"
`f : (x : α) → β x` picks `f x ∈ β x` for every `x`: an element of $`\prod_x \beta(x)`.
:::

# Inductive types

```lean -panel -stretch
inductive MyNat where
  | zero : MyNat
  | succ : MyNat → MyNat

#check @MyNat.rec
```

One declaration gives the type, its constructors and the recursor `MyNat.rec`, with a `motive : MyNat → Sort u`.

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

With `Bad`, `neg b := app b b` gives `neg (Bad.mk neg) : False`.

:::class "key"
The type may occur only to the right of an arrow.
:::

# Structures

One constructor, named fields.

```lean -panel -stretch
structure Point where
  x : ℕ
  y : ℕ
structure Point3D extends Point where
  z : ℕ
#check (Point.mk : ℕ → ℕ → Point)
```

Data with a property: `MyLinearMap` bundles `toFun` and `map_add`.

# Inductive types vs structures

:::table +colHeaders +rowSeps
*
  * use
  * when
  * examples
*
  * `structure`
  * one constructor, named fields
  * points, complex numbers, algebraic structures
*
  * `inductive`
  * several constructors
  * `ℕ`, lists, trees, `Option`, `Bool`
:::

A `structure` is sugar for a one-constructor `inductive`, plus field names, dot notation, defaults and `extends`.

# Pairs and Σ-types

```lean -panel -stretch
def aPair : (n : ℕ) × Fin (n + 1) :=
  ⟨3, Fin.last 3⟩
#eval aPair.1   -- 3
```

`(x : α) × β x`, also `Σ x, β x`: pairs `⟨a, b⟩` with `b : β a`.
A structure with two fields, `Sigma.fst` and `Sigma.snd`.

:::class "key"
In sets: the disjoint union $`\coprod_x \beta(x)`. If `β` is constant, `α × β`.
:::

# Sum and product

```lean -panel -stretch
-- Σ: 1 + 2 + 3 + 4
example : Fintype.card
    ((n : Fin 4) × Fin (n + 1)) = 10 := by decide
-- Π: 1 · 2 · 3 · 4
example : Fintype.card
    ((n : Fin 4) → Fin (n + 1)) = 24 := by decide
```

:::table +colHeaders
*
  * non-dependent
  * dependent
  * for propositions
*
  * `α → β`
  * `(x : α) → β x`
  * `∀ x, P x`
*
  * `α × β`
  * `(x : α) × β x`
  * `∃ x, P x`
:::

# Subtypes

`{x : α // P x}` with `P : α → Prop`: a pair whose second
component is a proof.

```lean -panel -stretch
def BigNat : Type := {n : ℕ // n > 5}

def seven : BigNat := ⟨7, by norm_num⟩
#eval seven.val  -- 7
```

:::class "key"
Proof irrelevance: two elements are equal iff their first components are.
:::

# Subtypes and sets

- Many Mathlib objects are subtypes, e.g. `{n : ℕ // Nat.Prime n}`.
- A set `s : Set α` selects elements, which keep their type `α`.
- The subtype `{x : α // P x}` is a _new_ type.
- `↥s` turns a set into the subtype of its members.

The chapter on sets and types spells this out.

# Type families

A type family is a function that returns a type.

```lean -panel -stretch
def BoolFamily : Bool → Type
  | true  => ℕ
  | false => String

def boolFamilyExample : (b : Bool) → BoolFamily b
  | true  => (42 : ℕ)
  | false => ("hello" : String)
```

# Fibers

The fiber of `f : α → β` over `b : β` is the subtype
`{a : α // f a = b}` — a type family indexed by `β`.

```lean -panel -stretch
def fiber (f : ℕ → ℕ) (b : ℕ) : Type :=
  {a : ℕ // f a = b}

def fiberExample : fiber (· * 2) 10 :=
  ⟨5, by norm_num⟩
```

# Vectors indexed by length

A vector of length `n` over `α` is a function `Fin n → α`.

```lean -panel -stretch
def myVec : Fin 3 → ℕ := ![10, 20, 30]

#eval myVec 0   -- 10
#eval myVec 2   -- 30
```

:::class "key"
Index 5 of a 3-element vector does not exist: `5` is not a term of
type `Fin 3`. Out-of-bounds is a compile-time error.
:::

# Matrices

An `m × n` matrix is a function `Fin m → Fin n → α`, or
`Matrix (Fin m) (Fin n) α` in Mathlib.

```lean -panel -stretch
def myMatrix : Fin 2 → Fin 3 → ℕ :=
  ![![1, 2, 3], ![4, 5, 6]]

#eval myMatrix 0 1  -- 2
#eval myMatrix 1 2  -- 6
```

:::class "key"
`A * B` needs `m × n` times `n × p`. A dimension mismatch is a type error.
:::

# Quotient types

`Quot r`: the type `α` seen up to a relation `r`. Examples: `ℤ`, `ℚ`, `ℝ`, `Multiset α`, `ZMod n`.

- `Quot.mk r` sends an element to its class
- `Quot.sound`: `r a b → Quot.mk r a = Quot.mk r b` — an axiom
- `Quot.lift f h`: needs a proof that `f` respects `r`
- `Quot.ind`: induction over classes

:::class "key"
`Quot.lift` is the mathematician's "check that this is well-defined".
:::

# Summary

- `(x : α) → β x`: dependent functions; `∀` for propositions, `→` if nothing depends.
- `inductive`: constructors and a recursor; only strictly positive.
- `structure`: one constructor, named fields.
- `(x : α) × β x`: dependent pairs, a disjoint union. Subtypes: the second component is a proof.
- `Quot r`: a type up to a relation.
