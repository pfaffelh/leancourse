import VersoSlides
import Verso.Doc.Concrete
import Mathlib

open VersoSlides

set_option pp.rawOnError true

/-
Deck for the chapter "Types" of part 1 (Lean and its type theory).
It follows the chapter section by section: where types come from, the
universe hierarchy, why `Prop` is special, inductive types, structures
and quotient types.
-/

namespace SlidesTypes
#doc (Slides) "Types" =>

```css
.reveal section p { font-size: 0.8em; line-height: 1.32; margin: 0.42em 0; }
.reveal section p.key, .reveal section .key p { color: #1b91ff; }
.reveal section table { font-size: 0.62em; margin: 0.2em auto 0.4em; }
.reveal section table th,
.reveal section table td { padding: 0.18em 0.9em; }
.reveal section li { font-size: 0.8em; }
```

# Types

Lean and its type theory — chapter 2

# Every term has a type

`x : α` means: `x` is a term of type `α`.

- `42 : ℕ`, `f : ℕ → ℝ`, `0 ≠ 1 : Prop`
- types may depend on terms: `f : (n : ℕ) → (Fin n → ℝ)`
- `h : P` with `P : Prop` is a _proof_
- `a : α` with `α : Type u` is _data_

:::class "key"
A type is itself a term, so it has a type as well.
:::

# Where types come from

Russell's paradox, 1902: $`R = \{x : x \notin x\}`. Two repairs in 1908.

:::table +colHeaders +rowSeps
*
  * 1908
  * restricts
  * `x ∈ x` is
*
  * Zermelo
  * which sets exist
  * a formula
*
  * Russell
  * what can be said
  * not a statement at all
:::

:::class "key"
In type theory the stratification is the language, and well-formedness is decidable.
:::

# The same move, three times

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

Then the Calculus of Constructions (1985) and inductive types (1990): the CIC, of which Lean's type theory is a variant.

:::class "key"
Self-application gives a contradiction; types forbid it.
:::

# The universe hierarchy

```lean -panel -stretch
#check (ℕ : Type)
#check (Prop : Type)
#check (Type : Type 1)
#check (Type 1 : Type 2)
example : Sort 0 = Prop := rfl
example : Sort 1 = Type := rfl
```

One rule: `Sort u : Sort (u+1)`. There is no `Type : Type`.

# How the universe is determined

```lean -panel -stretch
#check (ℕ → Type)             -- Type 1
#check (∀ α : Type, α → α)    -- Type 1
#check (∀ α : Type 5, α → α)  -- Type 6
```

_Predicative_: a type lands above everything it quantifies over.

:::class "key"
`Type : Type` would give Girard's paradox, a proof of `False`.
:::

# Why `Prop` is special: proof irrelevance

`Prop` records _that_ a statement holds, not _which_ proof.

```lean -panel -stretch
example (P : Prop) (h₁ h₂ : P) : h₁ = h₂ := rfl
```

```lean +error -panel -stretch
example (a b : ℕ) : a = b := rfl
```

# `Prop` is impredicative

```lean -panel -stretch
#check (∀ α : Type 5, α = α)  -- Prop
#check (∀ p : Prop, p → p)    -- Prop
#check (∀ p : Prop, p)        -- Prop
```

`∀ p : Prop, p → p` quantifies over a totality to which it belongs.

:::class "key"
A `∀` into `Prop` stays small; a `∀` into `Type u` must climb.
:::

# Russell's supremum

Russell's vicious circle principle forbids this; he needed the axiom of reducibility. Lean grants the circle in `Prop` and refuses it for data.

```lean -panel -stretch
-- the body ranges over all reals ...
#check fun (S : Set ℝ) (q : ℚ) =>
  (∃ x ∈ S, (q : ℝ) < x)       -- Prop
-- ... the cut is an ordinary Set ℚ
#check fun (S : Set ℝ) =>
  {q : ℚ | ∃ x ∈ S, (q : ℝ) < x}
```

# Is this consistent?

- Model `Prop` as fixed truth values: a `∀` over it is a meet, hence
  a member again.
- Lean is not first-order, so the model is built by hand.
- Carneiro 2019: relative to ZFC with $`n` inaccessibles. An error was
  found; unique typing and Pi-injectivity remain open.

:::class "key"
Consistency is well supported, not settled.
:::

# Restricted elimination

A proof carries no observable content, so no data can be read off it.

```lean +error -panel -stretch
example (a b : Prop) (h : a ∨ b) : Bool :=
  match h with
  | Or.inl _ => true
  | Or.inr _ => false
```

Exception, _subsingleton elimination_: `False`, `Eq`, `And`. Not `Or`, not `∃`.

# The tag has to stay hidden

```lean -panel -stretch
example {a : Prop} (h : a) :
    (Or.inl (b := a) h) = Or.inr (b := a) h :=
  rfl
```

A `which : a ∨ b → Bool` would give `true ≡ false`.

:::table +colHeaders +rowSeps
*
  * in `Prop`
  * in `Type`
  * stays hidden
*
  * `∃ x, q x`
  * `Σ x, q x`
  * the witness
*
  * `a ∨ ¬a`
  * `Decidable a`
  * the tag
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

- Types were invented to stop paradoxes of self-application.
- Universes: `Prop`, `Type 0 : Type 1 : ...`; there is no `Type : Type`.
- `Prop` is proof irrelevant, impredicative, and eliminates only into `Prop`.
- New types: inductive types, structures, quotients.
- Constructors build values; the recursor uses them.
