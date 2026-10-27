import VersoSlides
import Verso.Doc.Concrete
import Mathlib

open VersoSlides

set_option pp.rawOnError true

/-
Deck for the chapter "Types and terms II: structures, pairs,
subtypes, quotients" of part 1 (Lean and its type theory). It follows
the chapter section by section: structures and their values, data
with a property, Σ-types, subtypes, type families, quotient types,
and the table of the four steps.
-/

namespace SlidesTypeFormers
#doc (Slides) "Types and terms II: structures, pairs, subtypes, quotients" =>

```css
.reveal section p { font-size: 0.8em; line-height: 1.32; margin: 0.42em 0; }
.reveal section p.key, .reveal section .key p { color: #1b91ff; }
.reveal section table { font-size: 0.62em; margin: 0.2em auto 0.4em; }
.reveal section table th,
.reveal section table td { padding: 0.18em 0.9em; }
.reveal section li { font-size: 0.8em; }
.reveal section .small table, .reveal section table.small { font-size: 0.5em; }
.reveal section .small table code, .reveal section table.small code { font-size: 0.95em; }
.reveal section .small td, .reveal section table.small td { padding: 0.1em 0.6em; }
```

# Types and terms II

Lean and its type theory — chapter 3: structures, pairs, subtypes, quotients

:::class "key"
Each type former again in four steps: formation, construction, use, computation.
:::

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
- _Use_: projections `Point.x p`, also `p.x`
- _Computation_: `(Point.mk 3 4).x` reduces to `3`; η: `p ≡ Point.mk p.x p.y`

# Four forms, one constructor

```lean -panel -stretch
def origin : Point := { x := 0, y := 0 }
def p1 : Point := ⟨1, 2⟩
def p2 : Point := Point.mk 3 4
def p3 : Point where
  x := 0
  y := 0
#check ({ x := 0, y := 0 } : Point)
```

`where` is the record form over several lines — unrelated to the `|`-branches of pattern matching.

# Reading and updating fields

```lean -panel -stretch
#eval p1.x          -- 1

def p4 : Point := { p1 with y := 10 }
-- p4.x = 1, p4.y = 10
```

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

# Operations and dot notation

```lean -panel -stretch
def Point.normSq (p : Point) : ℕ :=
  p.x * p.x + p.y * p.y

#eval p2.normSq    -- 25
```

`p2 : Point`, so Lean looks for `Point.normSq`.

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

# `Fin n` is a structure

```lean -panel -stretch
#check @Fin.mk
-- {n : ℕ} → (val : ℕ) → val < n → Fin n

example : Fin 3 := ⟨2, by simp⟩
example (n : ℕ) (h : 0 < n) : Fin n := ⟨0, h⟩
```

An element is a number together with a proof that it is less than `n`.

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

A `structure` is sugar for a one-constructor `inductive`, plus field names, projections with dot notation, defaults and `extends`.

# Pairs and Σ-types

```lean -panel -stretch
def aPair : (n : ℕ) × Fin (n + 1) :=
  ⟨3, Fin.last 3⟩
#eval aPair.1   -- 3
example (p : ℕ × ℕ) : p = (p.1, p.2) := rfl
```

- _Formation_: `(x : α) × β x`, also `Σ x, β x`; `α × β` if nothing depends
- _Construction_: `⟨a, b⟩`
- _Use_: `.1`, `.2` (also `.fst`, `.snd`)
- _Computation_: `⟨a, b⟩.1 ⟶ a`

:::class "key"
In sets: the disjoint union $`\coprod_x \beta(x)`.
:::

# Sum and product

`Fintype.card α` is the number of elements; `decide` computes both sides.

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

```lean -panel -stretch
def BigNat : Type := {n : ℕ // n > 5}

def seven : BigNat := ⟨7, by simp⟩
#eval seven.val  -- 7
```

- _Formation_: `{x : α // P x}`, i.e. `Subtype P`
- _Construction_: `⟨a, h⟩` with `h : P a`
- _Use_: `.val`, `.property`
- _Computation_: `⟨a, h⟩.val ⟶ a`

:::class "key"
Proof irrelevance: two elements are equal iff their values are (`Subtype.ext`).
:::

# Subtypes and sets

- Many Mathlib objects are subtypes, e.g. `{n : ℕ // Nat.Prime n}`.
- `Fin n` carries the same data as `{i : ℕ // i < n}`, but is a type of its own.
- A set `s : Set α` selects elements, which keep their type `α`.
- The subtype `{x : α // P x}` is a _new_ type.

# Type families

A type family is a function that returns a type.

```lean -panel -stretch
def BoolFamily : Bool → Type
  | true  => ℕ
  | false => String

def fiber (f : ℕ → ℕ) (b : ℕ) : Type :=
  {a : ℕ // f a = b}

def fiberExample : fiber (· * 2) 10 := ⟨5, rfl⟩
```

# Vectors and matrices

`![a, b, c]` is the function on `Fin 3` with values `a`, `b`, `c`.

```lean -panel -stretch
def myVec : Fin 3 → ℕ := ![10, 20, 30]
#eval myVec 2   -- 30

def myMatrix : Fin 2 → Fin 3 → ℕ :=
  ![![1, 2, 3], ![4, 5, 6]]
#eval myMatrix 1 2  -- 6
```

:::class "key"
Index 5 of a 3-element vector does not exist. A dimension mismatch is a type error.
:::

# Indexed families

```lean -panel -stretch
inductive Vec (α : Type) : ℕ → Type where
  | nil : Vec α 0
  | cons {n : ℕ} : α → Vec α n →
      Vec α (n + 1)

def Vec.head {α : Type} {n : ℕ} :
    Vec α (n + 1) → α
  | .cons a _ => a
```

`α` is a _parameter_, fixed for all constructors. The `ℕ` is an _index_: each constructor chooses it.

:::class "key"
`head` needs no case for `nil`: its index `0` is not `n + 1`.
:::

# Inductive predicates

```lean -panel -stretch
inductive MyEven : ℕ → Prop where
  | zero : MyEven 0
  | add_two (n : ℕ) : MyEven n → MyEven (n + 2)

example : ¬ MyEven 1 := by
  intro h
  cases h
```

The constructors are the only ways to prove `MyEven n`. `cases h` keeps the constructors whose index fits.

:::class "key"
`≤` on `ℕ` and `=` are inductive predicates of this kind.
:::

# Quotient types

`Quot r`: the type `α` seen up to a relation `r`. Examples: `ℤ`, `ℚ`, `ℝ`, `Multiset α`, `ZMod n`.

- _Formation_: `Quot r`
- _Construction_: `Quot.mk r a`, the class of `a`
- _Use_: `Quot.lift f h`, with `h` a proof that `f` respects `r`
- _Computation_: `Quot.lift f h (Quot.mk r a) ⟶ f a`

:::class "key"
`Quot.lift` is the mathematician's "check that this is well-defined".
:::

# One axiom

```lean -panel -stretch
#check @Quot.sound  -- r a b → Quot.mk r a = Quot.mk r b
#print axioms Quot.sound
```

That related elements have the _same_ class does not follow from the four steps. Lean assumes it as an _axiom_.

# The four steps at a glance

::::class "small"
:::table +colHeaders +rowSeps
*
  * type
  * formation
  * construction
  * use
  * computation
*
  * function
  * `(x : α) → β x`
  * `fun x => e`
  * `f a`
  * β
*
  * inductive
  * `inductive T`
  * constructors
  * pattern matching
  * ι
*
  * structure
  * `structure S`
  * `⟨a, b⟩`
  * `s.x`
  * `(S.mk a b).x ⟶ a`
*
  * Σ-type
  * `(x : α) × β x`
  * `⟨a, b⟩`
  * `.1`, `.2`
  * `⟨a, b⟩.1 ⟶ a`
*
  * subtype
  * `{x : α // P x}`
  * `⟨a, h⟩`
  * `.val`
  * `⟨a, h⟩.val ⟶ a`
*
  * indexed family
  * `inductive T : I → Sort u`
  * constructors
  * `cases`
  * ι
*
  * quotient
  * `Quot r`
  * `Quot.mk r a`
  * `Quot.lift f h`
  * `… ⟶ f a`
:::
::::

:::class "key"
Chapter 1.4 states these steps as the rules of Lean's type theory.
:::

# Summary

- `structure`: one constructor, named fields; values by `⟨…⟩`, `{ x := … }`, `where`; fields by projections.
- A field may be a proof: data with a property.
- `(x : α) × β x`: dependent pairs, a disjoint union. Subtypes: the second component is a proof.
- Type families are functions into a universe; with `inductive`, the constructors fix the index.
- `Quot r`: a type up to a relation, with the axiom `Quot.sound`.
