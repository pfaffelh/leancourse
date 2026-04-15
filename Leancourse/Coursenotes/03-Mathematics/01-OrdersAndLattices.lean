import VersoManual
import Manual.Meta
import Leancourse.Misc.Defs
import Mathlib

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open MyDef

set_option pp.rawOnError true
set_option verso.docstring.allowMissing true

#doc (Manual) "Orders, Lattices, and Complete Lattices" =>
%%%
htmlSplit := .never
tag := "orders-and-lattices"
%%%

In this chapter we explore how Mathlib formalizes the fundamental notions of
order theory. Ordered structures pervade all of mathematics: partial orders
appear in set inclusion, divisibility of natural numbers, and subgroup
relations; lattices arise whenever we can form meets and joins; and complete
lattices are essential for fixed-point theorems and topology.

# Notation and naming conventions
%%%
tag := "orders-notation"
%%%

Several symbols below are unicode characters typed in VS Code via a
backslash escape (e.g. `\le` produces `≤`).  Hover over a symbol in the
editor to see how to type it.

| Symbol  | Lean name             | Reads as                        | Typed as                |
|---------|-----------------------|---------------------------------|-------------------------|
| `≤`     | `LE.le a b`           | "a less than or equal to b"     | `\le`                   |
| `<`     | `LT.lt a b`           | "a strictly less than b"        | `\lt`                   |
| `⊆`     | `Set.Subset s t`      | "s is a subset of t"            | `\sub`                  |
| `⊔`     | `Sup.sup a b`         | "a join b" / "a sup b"          | `\sup`                  |
| `⊓`     | `Inf.inf a b`         | "a meet b" / "a inf b"          | `\inf`                  |
| `⊤`     | `Top.top`             | "top"                           | `\top`                  |
| `⊥`     | `Bot.bot`             | "bottom"                        | `\bot`                  |
| `sSup`  | `sSup s`              | "supremum of the set s"         | (ASCII)                 |
| `sInf`  | `sInf s`              | "infimum of the set s"          | (ASCII)                 |
| `iSup`  | `iSup f`              | "indexed supremum"              | (ASCII)                 |
| `iInf`  | `iInf f`              | "indexed infimum"               | (ASCII)                 |
| `→o`    | `OrderHom α β`        | "order homomorphism α to β"     | `\to o` or `\too`       |

Naming hints:

- The prefix `s` in `sSup`, `sInf` stands for *set*: it takes a `Set α`.
- The prefix `i` in `iSup`, `iInf` stands for *indexed*: it takes a function.
- The bare operators `⊔` and `⊓` are *binary*; `sSup`, `sInf`, `iSup`, `iInf` are their *set/indexed* counterparts.
- Lemma naming follows the convention `le_sup_left`, `inf_le_right`, `le_antisymm`, etc.: the conclusion is named first, then the hypotheses in order.

# Partial orders
%%%
tag := "partial-orders"
%%%

A *partial order* on a type `α` is a reflexive, transitive, and antisymmetric
relation `≤`. In Mathlib this is captured by the typeclass `PartialOrder α`,
which extends `Preorder α` (reflexive and transitive) with antisymmetry.

Key lemmas:
- `le_refl a : a ≤ a`
- `le_trans : a ≤ b → b ≤ c → a ≤ c`
- `le_antisymm : a ≤ b → b ≤ a → a = b`

A *linear order* (`LinearOrder α`) additionally satisfies totality: for every
`a b : α`, either `a ≤ b` or `b ≤ a`. The natural numbers, integers, and
reals all carry linear orders.

```lean
-- Lean already knows that ℕ is linearly ordered:
#check (inferInstance : LinearOrder ℕ)

-- Every linear order is a partial order:
#check (inferInstance : PartialOrder ℕ)

-- A simple proof using transitivity
example (a b c : ℕ) (hab : a ≤ b) (hbc : b ≤ c) : a ≤ c :=
  le_trans hab hbc

-- Antisymmetry
example (a b : ℕ) (hab : a ≤ b) (hba : b ≤ a) : a = b :=
  le_antisymm hab hba
```

The strict order `<` is defined in terms of `≤`:
`a < b ↔ a ≤ b ∧ a ≠ b` (or equivalently `a ≤ b ∧ ¬ b ≤ a`).

```lean
example (a b : ℕ) (h : a < b) : a ≤ b :=
  le_of_lt h

example (a b : ℕ) (h : a < b) : a ≠ b :=
  ne_of_lt h
```

# The power set as a partial order
%%%
tag := "powerset-order"
%%%

For any type `α`, the type `Set α` carries a partial order given by set
inclusion `⊆`. This is a canonical example of a partial order that is not
linear in general.

```lean
example (A B C : Set ℕ) (hAB : A ⊆ B) (hBC : B ⊆ C) : A ⊆ C :=
  Set.Subset.trans hAB hBC

example (A B : Set ℕ) (hAB : A ⊆ B) (hBA : B ⊆ A) : A = B :=
  Set.Subset.antisymm hAB hBA
```

# Lattices
%%%
tag := "lattices"
%%%

A *lattice* is a partial order in which every pair of elements has a least
upper bound (supremum, join) and a greatest lower bound (infimum, meet).

In Mathlib:
- `⊔` (typed `\sup`) denotes the join (supremum of two elements).
- `⊓` (typed `\inf`) denotes the meet (infimum of two elements).
- The typeclass is `Lattice α`.

Key API:
- `le_sup_left : a ≤ a ⊔ b`
- `le_sup_right : b ≤ a ⊔ b`
- `sup_le : a ≤ c → b ≤ c → a ⊔ b ≤ c`
- `inf_le_left : a ⊓ b ≤ a`
- `inf_le_right : a ⊓ b ≤ b`
- `le_inf : c ≤ a → c ≤ b → c ≤ a ⊓ b`

```lean
-- Sets form a lattice with ∪ as ⊔ and ∩ as ⊓
example (A B : Set ℕ) : A ⊆ A ∪ B :=
  Set.subset_union_left

example (A B C : Set ℕ) (hA : C ⊆ A) (hB : C ⊆ B) : C ⊆ A ∩ B :=
  Set.subset_inter hA hB

-- In a general lattice:
example {α : Type*} [Lattice α] (a b c : α) (ha : a ≤ c) (hb : b ≤ c) :
    a ⊔ b ≤ c :=
  sup_le ha hb

example {α : Type*} [Lattice α] (a b : α) : a ⊓ b ≤ a :=
  inf_le_left
```

# Complete lattices
%%%
tag := "complete-lattices"
%%%

A *complete lattice* is a partial order in which every subset has a supremum
and an infimum (not just pairs). In Mathlib the typeclass is
`CompleteLattice α`.

The operations are:
- `sSup S` : the supremum of a set `S : Set α`
- `sInf S` : the infimum of a set `S : Set α`
- `⊤` (`\top`) : the greatest element (= `sSup Set.univ`)
- `⊥` (`\bot`) : the least element (= `sInf Set.univ`)
- `iSup` and `iInf` for indexed suprema and infima.

```lean
-- Set α is a complete lattice
#check (inferInstance : CompleteLattice (Set ℕ))

-- sSup of a family of sets is their union
example (S : Set (Set ℕ)) : sSup S = ⋃₀ S :=
  rfl

-- Every element of the family is below the sSup
example {α : Type*} [CompleteLattice α] (s : Set α) (a : α) (ha : a ∈ s) :
    a ≤ sSup s :=
  le_sSup ha
```

# Monotone and antitone functions
%%%
tag := "monotone-antitone"
%%%

A function `f : α → β` between preorders is *monotone* if `a ≤ b → f a ≤ f b`,
and *antitone* if `a ≤ b → f b ≤ f a`. Mathlib provides `Monotone f` and
`Antitone f`.

```lean
example : Monotone (fun n : ℕ ↦ n + 1) :=
  fun _ _ h ↦ Nat.add_le_add_right h 1

-- A constant function is both monotone and antitone
example {α β : Type*} [Preorder α] [Preorder β] (c : β) :
    Monotone (fun _ : α ↦ c) :=
  fun _ _ _ ↦ le_refl c
```

There is also `StrictMono f` for strictly increasing functions.

# The Knaster-Tarski fixed point theorem
%%%
tag := "fixed-points"
%%%

The *Knaster-Tarski theorem* is one of the cornerstones of fixed point
theory.  It generalizes Tarski's earlier fixed point theorem for the
real line and has applications in logic, denotational semantics, and
set theory (e.g. the Schröder-Bernstein theorem).

*Theorem* (Knaster-Tarski).  Let `α` be a complete lattice and let
`f : α → α` be a monotone function. Then:

1. `f` has a least fixed point, given by `sInf {x | f x ≤ x}`.
2. `f` has a greatest fixed point, given by `sSup {x | x ≤ f x}`.
3. Moreover, the set of fixed points of `f` is itself a complete
   lattice under the induced order.

The proof of the first part is short and instructive.  Let
`S = {x | f x ≤ x}` (the *prefixed points*) and set `a = sInf S`.
Since `f` is monotone and `a ≤ x` for every `x ∈ S`, we get
`f a ≤ f x ≤ x` for all `x ∈ S`, so `f a` is a lower bound of `S`,
hence `f a ≤ a`.  Thus `a ∈ S`.  Applying `f` monotonically gives
`f (f a) ≤ f a`, so `f a ∈ S`, hence `a ≤ f a`.  Antisymmetry yields
`f a = a`, and any other fixed point `y = f y` belongs to `S`, so
`a ≤ y`.

In Mathlib this theorem is available through the `OrderHom` API. The
least fixed point is `OrderHom.lfp` and the greatest is `OrderHom.gfp`:

The least fixed point and the key lemmas:

{docstring OrderHom.lfp}

{docstring OrderHom.map_lfp}

{docstring OrderHom.lfp_le}

Dually, the greatest fixed point:

{docstring OrderHom.gfp}

{docstring OrderHom.map_gfp}

{docstring OrderHom.le_gfp}

Note that `α →o α` is the type of monotone self-maps of `α` (the arrow
`→o` denotes an `OrderHom`).  A useful small example:

```lean
-- The lfp of the constant ∅ map on Set X is ∅:
example {X : Type*} :
    OrderHom.lfp
      ⟨(fun _ : Set X ↦ (∅ : Set X)),
        fun _ _ _ ↦ le_refl _⟩
      = ∅ := by
  apply le_antisymm
  · exact OrderHom.lfp_le _ (le_refl _)
  · exact bot_le
```

*Applications.*

- *Recursive definitions.*  The semantics of recursion in programming
  languages is given by least fixed points of monotone functionals on
  a domain of partial functions.
- *The Schröder-Bernstein theorem.*  Given injections `f : α → β` and
  `g : β → α`, one constructs a bijection by taking the least fixed
  point of a certain monotone operator on `Set α`.
- *Inductively defined sets.*  Many sets in mathematics (the natural
  numbers, syntactic terms, well-founded relations) are defined as
  least fixed points of monotone operators.

# Summary of key API
%%%
tag := "order-api-summary"
%%%

Here is a quick reference for the most important order-theoretic lemmas:

| Lemma | Statement |
|-------|-----------|
| `le_refl` | `a ≤ a` |
| `le_trans` | `a ≤ b → b ≤ c → a ≤ c` |
| `le_antisymm` | `a ≤ b → b ≤ a → a = b` |
| `le_sup_left` | `a ≤ a ⊔ b` |
| `le_sup_right` | `b ≤ a ⊔ b` |
| `sup_le` | `a ≤ c → b ≤ c → a ⊔ b ≤ c` |
| `inf_le_left` | `a ⊓ b ≤ a` |
| `inf_le_right` | `a ⊓ b ≤ b` |
| `le_inf` | `c ≤ a → c ≤ b → c ≤ a ⊓ b` |
| `le_sSup` | `a ∈ s → a ≤ sSup s` |
| `sSup_le` | `(∀ a ∈ s, a ≤ b) → sSup s ≤ b` |

The `omega` tactic is very useful for goals involving natural number and integer
inequalities. For more general ordered structures, `gcongr` can help with
monotonicity goals.
