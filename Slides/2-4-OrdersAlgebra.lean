import VersoSlides
import Verso.Doc.Concrete
import Mathlib

open VersoSlides

set_option pp.rawOnError true

/-
Deck for the chapters "Orders, Lattices, and Complete Lattices" and
"The Algebraic Hierarchy in Mathlib" of part 2 (Mathematics), read in
one lecture. It follows both chapters section by section: partial
orders, the power set, lattices, complete lattices, monotone maps,
Knaster–Tarski; then monoids, groups, rings and fields, morphisms,
substructures, quotients, `ext`, navigating the hierarchy.
-/

namespace SlidesOrdersAlgebra

#doc (Slides) "Orders and the algebraic hierarchy" =>

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

# Orders and the algebraic hierarchy

Mathematics — chapters 4 and 5

:::class "key"
Orders and algebraic structures are typeclass hierarchies. Each result is stated for the weakest class it needs.
:::

# Notation for orders

::::class "small"
:::table +colHeaders +rowSeps
*
  * symbol
  * reads as
  * typed as
*
  * `≤`, `<`
  * less than or equal, strictly less
  * `\le`, `\lt`
*
  * `⊔`, `⊓`
  * join (sup) and meet (inf) of two elements
  * `\sup`, `\inf`
*
  * `⊤`, `⊥`
  * top and bottom
  * `\top`, `\bot`
*
  * `sSup s`, `sInf s`
  * supremum, infimum of a set `s : Set α`
  * ASCII
*
  * `iSup f`, `iInf f`
  * indexed supremum, infimum of `f : ι → α`
  * ASCII
*
  * `α →o β`
  * monotone maps, `OrderHom α β`
  * `\to o`
:::
::::

Names read the conclusion left to right, hypotheses after `of`: `le_sup_left` (`a ≤ a ⊔ b`), `inv_inv` (`a⁻¹⁻¹ = a`), `le_of_lt` (`a < b → a ≤ b`).

# Partial orders

:::table +colHeaders +rowSeps
*
  * class
  * adds
  * lemma
*
  * `Preorder α`
  * reflexive, transitive
  * `le_refl`, `le_trans`
*
  * `PartialOrder α`
  * antisymmetric
  * `le_antisymm`
*
  * `LinearOrder α`
  * total: `a ≤ b ∨ b ≤ a`
  * `le_total`
:::

`ℕ`, `ℤ`, `ℚ`, `ℝ` carry linear orders. `<` is a separate field with `a < b ↔ a ≤ b ∧ ¬ b ≤ a`; in a partial order: `a ≤ b ∧ a ≠ b`.

:::class "key"
`PartialOrder` extends `Preorder` (chapter 1.7): every partial order is a preorder.
:::

# Partial orders in Lean

```lean -panel -stretch
#check (inferInstance : LinearOrder ℕ)

example (a b c : ℕ) (hab : a ≤ b) (hbc : b ≤ c) :
    a ≤ c :=
  le_trans hab hbc

example (a b : ℕ) (hab : a ≤ b) (hba : b ≤ a) :
    a = b :=
  le_antisymm hab hba

example (a b : ℕ) (h : a < b) : a ≤ b := le_of_lt h
example (a b : ℕ) (h : a < b) : a ≠ b := ne_of_lt h
```

# The power set as a partial order

`Set α` is partially ordered by `⊆`. In general the order is not linear: `{0}` and `{1}` are incomparable.

```lean -panel -stretch
example (A B C : Set ℕ) (hAB : A ⊆ B) (hBC : B ⊆ C) :
    A ⊆ C :=
  Set.Subset.trans hAB hBC

example (A B : Set ℕ) (hAB : A ⊆ B) (hBA : B ⊆ A) :
    A = B :=
  Set.Subset.antisymm hAB hBA

example (A B : Set ℕ) : (A ≤ B) = (A ⊆ B) := rfl
```

# Lattices

A *lattice* is a partial order in which any two elements have a least upper bound `a ⊔ b` (join) and a greatest lower bound `a ⊓ b` (meet). Class: `Lattice α`.

:::table +colHeaders +rowSeps
*
  * join
  * meet
*
  * `le_sup_left : a ≤ a ⊔ b`
  * `inf_le_left : a ⊓ b ≤ a`
*
  * `le_sup_right : b ≤ a ⊔ b`
  * `inf_le_right : a ⊓ b ≤ b`
*
  * `sup_le : a ≤ c → b ≤ c → a ⊔ b ≤ c`
  * `le_inf : c ≤ a → c ≤ b → c ≤ a ⊓ b`
:::

:::class "key"
In `Set α`, the join is `∪` and the meet is `∩`.
:::

# Lattices in Lean

```lean -panel -stretch
example (A B : Set ℕ) : A ⊆ A ∪ B :=
  Set.subset_union_left

example (A B C : Set ℕ) (hA : C ⊆ A) (hB : C ⊆ B) :
    C ⊆ A ∩ B :=
  Set.subset_inter hA hB

example {α : Type*} [Lattice α] (a b c : α)
    (ha : a ≤ c) (hb : b ≤ c) : a ⊔ b ≤ c :=
  sup_le ha hb

example {α : Type*} [Lattice α] (a b : α) :
    a ⊓ b ≤ a :=
  inf_le_left
```

# Complete lattices

A *complete lattice* is a partial order in which every subset has a supremum `sSup s` and an infimum `sInf s`. Class: `CompleteLattice α`. Then `⊤ = sSup Set.univ` and `⊥ = sInf Set.univ`.

```lean -panel -stretch
#check (inferInstance : CompleteLattice (Set ℕ))

example (S : Set (Set ℕ)) : sSup S = ⋃₀ S := rfl

example {α : Type*} [CompleteLattice α] (s : Set α)
    (a : α) (ha : a ∈ s) : a ≤ sSup s :=
  le_sSup ha
```

`sSup_le : (∀ a ∈ s, a ≤ b) → sSup s ≤ b` is the other half.

# Monotone and antitone functions

For `f : α → β` between preorders:

- `Monotone f`: `a ≤ b → f a ≤ f b`
- `Antitone f`: `a ≤ b → f b ≤ f a`
- `StrictMono f`: `a < b → f a < f b`

```lean -panel -stretch
example : Monotone (fun n : ℕ ↦ n + 1) :=
  fun _ _ h ↦ Nat.add_le_add_right h 1

example {α β : Type*} [Preorder α] [Preorder β]
    (c : β) : Monotone (fun _ : α ↦ c) :=
  fun _ _ _ ↦ le_refl c
```

# The Knaster–Tarski theorem

*Theorem (Knaster–Tarski).* Let `α` be a complete lattice and `f : α → α` monotone. Then

1. `f` has a least fixed point, `sInf {x | f x ≤ x}`;
2. `f` has a greatest fixed point, `sSup {x | x ≤ f x}`;
3. the fixed points of `f` form a complete lattice in the induced order.

:::class "key"
The theorem needs only completeness of `α` and monotonicity of `f`.
:::

# Proof of part 1

Let `S = {x | f x ≤ x}` (the _prefixed points_) and `a = sInf S`.

- Step 1: for `x ∈ S`, `a ≤ x`, so `f a ≤ f x ≤ x`. Hence `f a` is a lower bound of `S`, so `f a ≤ a`, and `a ∈ S`.
- Step 2: by monotonicity `f (f a) ≤ f a`, so `f a ∈ S`, hence `a ≤ f a`.
- Step 3: antisymmetry gives `f a = a`.
- Step 4: every fixed point `y = f y` lies in `S`, so `a ≤ y`.

Part 2 is the dual statement.

# Knaster–Tarski in Mathlib

`α →o α` is the type of monotone maps `α → α` (`OrderHom`): a function bundled with the proof that it is monotone.

::::class "small"
:::table +colHeaders +rowSeps
*
  * least fixed point
  * greatest fixed point
*
  * `OrderHom.lfp f`
  * `OrderHom.gfp f`
*
  * `map_lfp : f (lfp f) = lfp f`
  * `map_gfp : f (gfp f) = gfp f`
*
  * `lfp_le : f a ≤ a → lfp f ≤ a`
  * `le_gfp : a ≤ f a → a ≤ gfp f`
:::
::::

:::class "key"
`lfp_le` is the proof principle: to bound the least fixed point, find a prefixed point.
:::

# A least fixed point

```lean -panel -stretch
example {X : Type*} :
    OrderHom.lfp
      ⟨(fun _ : Set X ↦ (∅ : Set X)),
        fun _ _ _ ↦ le_refl _⟩
      = ∅ := by
  apply le_antisymm
  · exact OrderHom.lfp_le _ (le_refl _)
  · exact bot_le
```

`⟨f, proof of monotonicity⟩` builds `α →o α`; `bot_le : ⊥ ≤ a`, and `∅ = ⊥` in `Set X`.

Uses: semantics of recursive definitions; Schröder–Bernstein (an operator on `Set α`); inductive types (1.3: strictly positive = monotone).

# Notation for algebra

::::class "small"
:::table +colHeaders +rowSeps
*
  * multiplicative
  * additive
  * reads as
*
  * `a * b`, `1`
  * `a + b`, `0`
  * operation, neutral element
*
  * `a⁻¹` (`\inv`)
  * `-a`
  * inverse
*
  * `Monoid`, `Group`
  * `AddMonoid`, `AddGroup`
  * classes
*
  * `mul_assoc`, `mul_one`
  * `add_assoc`, `add_zero`
  * lemmas
*
  * `→*` (`MonoidHom`)
  * `→+` (`AddMonoidHom`)
  * homomorphisms
:::
::::

Rings combine both: `→+*` (`RingHom`). `R ⧸ I` (`\quot`) is a quotient; `⊥`, `⊤` are the smallest and largest substructure.

:::class "key"
Every notion exists twice, multiplicative and additive; additive lemmas start with `add_`.
:::

# From operations to monoids

:::table +colHeaders +rowSeps
*
  * class
  * provides
*
  * `Mul α`, `Add α`
  * the operation `*`, `+`
*
  * `One α`, `Zero α`
  * the element `1`, `0`
*
  * `MulOneClass α`
  * `1 * a = a`, `a * 1 = a`
*
  * `Monoid α`
  * moreover `*` associative
*
  * `CommMonoid α`
  * moreover `*` commutative
:::

```lean -panel -stretch
#check (inferInstance : AddCommMonoid ℕ)
example (a b c : ℕ) : a + b + c = a + (b + c) :=
  add_assoc a b c
```

# Groups

A *group* is a monoid in which every element has an inverse: `Group α` (`a⁻¹`), `AddGroup α` (`-a`), and `CommGroup α`, `AddCommGroup α`.

```lean -panel -stretch
#check (inferInstance : AddCommGroup ℤ)

example {G : Type*} [Group G] (a : G) : a * a⁻¹ = 1 :=
  mul_inv_cancel a

example {G : Type*} [Group G] (a b : G) :
    (a * b)⁻¹ = b⁻¹ * a⁻¹ :=
  mul_inv_rev a b
```

:::class "key"
A lemma proved for `[Group G]` applies to every group in Mathlib.
:::

# Rings and fields

- `Ring α`: `+` an abelian group, `*` a monoid, distributive
- `CommRing α`: moreover `*` commutative
- `Field α`: commutative ring, `0 ≠ 1`, every `a ≠ 0` invertible; `0⁻¹ = 0` by convention (chapter 2.1)

```lean -panel -stretch
example (a b c : ℝ) : a * (b + c) = a * b + a * c :=
  mul_add a b c

-- `₀`: lemma for structures with a zero
-- (`GroupWithZero`), needs `a ≠ 0`
example (a : ℝ) (ha : a ≠ 0) : a * a⁻¹ = 1 :=
  mul_inv_cancel₀ ha
```

# The integers mod n

`ZMod n` is a commutative ring for every `n`, a field only for prime `n`. Instance search cannot prove primality, so the field instance asks for `[Fact p.Prime]` (chapter 1.6).

```lean -panel -stretch
example (n : ℕ) : CommRing (ZMod n) := inferInstance
example (p : ℕ) [Fact p.Prime] : Field (ZMod p) :=
  inferInstance

example : (3 : ZMod 7) * 5 = 1 := by decide
example : (2 : ZMod 4) * 2 = 0 := by decide
```

:::class "key"
The instance is a function of `n`: `CommRing (ZMod n)` is a type that depends on a number.
:::

# Ordered rings

The order is a separate class. `IsStrictOrderedRing ℝ`, a `Prop`-valued class: `a ≤ b → a + c ≤ b + c`, `0 ≤ 1`, `0 ≠ 1`, `0 < c → a < b → c * a < c * b`.

```lean -panel -stretch
#check (inferInstance : LinearOrder ℝ)
#check (inferInstance : IsStrictOrderedRing ℝ)

example (a b c : ℝ) (h : a ≤ b) : a + c ≤ b + c := by
  linarith
```

:::class "key"
`ℝ` is a field, a linear order, and a strictly ordered ring: three instances, combined by instance search.
:::

# Morphisms

Morphisms are _bundled_: the function plus proofs that it preserves the operations, applied as a function through `DFunLike` (1.7). `M →* N` preserves `*`, `1`; `M →+ N` preserves `+`, `0`; `R →+* S` all four.

```lean -panel -stretch
example (f : ℤ →+* ℚ) (a b : ℤ) :
    f (a * b) = f a * f b :=
  map_mul f a b

example (f : ℤ →+* ℚ) : f 0 = 0 := map_zero f
```

`map_mul`, `map_add`, `map_zero` hold for every bundled morphism type (classes `MulHomClass`, `AddMonoidHomClass`).

# Substructures

`Subgroup G`, `Subring R`, `Ideal R` are bundled too: a carrier set and the proofs that it is closed under the operations.

```lean -panel -stretch
example {G : Type*} [Group G] (H : Subgroup G) (a b : G)
    (ha : a ∈ H) (hb : b ∈ H) : a * b ∈ H :=
  H.mul_mem ha hb

example {G : Type*} [Group G] (H : Subgroup G) :
    (1 : G) ∈ H :=
  H.one_mem
```

:::class "key"
`a ∈ H` means `a ∈ H.carrier`. Closure: fields `mul_mem'`, `one_mem'`, `inv_mem'`; use the lemmas `H.mul_mem`, `H.one_mem`, `H.inv_mem` (for an ideal: `I.add_mem`).
:::

# Subgroups form a complete lattice

```lean -panel -stretch
#check (inferInstance : CompleteLattice (AddSubgroup ℤ))
```

- `⊥`: the trivial subgroup; `⊤`: the whole group
- `H ⊓ K`: the intersection
- `H ⊔ K`: the subgroup generated by `H ∪ K`, not the union

:::class "key"
The order API applies to subgroups, ideals and subrings.
:::

# Quotient structures

For a normal subgroup `N` of `G`, the quotient `G ⧸ N` is a group; for an ideal `I` of `R`, `R ⧸ I` is a ring. Normality is an instance `[N.Normal]`.

```lean -panel -stretch
example {G : Type*} [Group G] (N : Subgroup G)
    [N.Normal] : Group (G ⧸ N) :=
  inferInstance
example (R : Type*) [CommRing R] (I : Ideal R) :
    CommRing (R ⧸ I) :=
  inferInstance
```

# The integers mod 6 as a quotient

```lean -panel -stretch
example (I : Ideal ℤ) : ℤ →+* ℤ ⧸ I := Ideal.Quotient.mk I
#check (Int.quotientSpanNatEquivZMod 6 :
  ℤ ⧸ Ideal.span {(6 : ℤ)} ≃+* ZMod 6)
```

- `Ideal.span s`: the ideal generated by `s` (here `6ℤ`).
- `Ideal.Quotient.mk I`: the quotient map, a ring homomorphism.
- `ZMod n` is not defined as a quotient, but it is one up to a ring isomorphism `≃+*`.

# `ext` for structures

Two subgroups with the same elements are equal; two morphisms that agree everywhere are equal. `ext` reduces to these; it uses lemmas tagged `@[ext]`, e.g. `Subgroup.ext`, `RingHom.ext`.

```lean -panel -stretch
example {G : Type*} [Group G] (H K : Subgroup G)
    (h : ∀ g, g ∈ H ↔ g ∈ K) : H = K := by
  ext g
  exact h g

example {R S : Type*} [Ring R] [Ring S] (f g : R →+* S)
    (h : ∀ r, f r = g r) : f = g := by
  ext r
  exact h r
```

# Navigating the hierarchy

- `#check (inferInstance : C α)` and `#synth C α`: does `α` carry `C`?
- `#print C`: the fields and parents of a class
- `exact?`, `apply?`, `#loogle`: lemma search
- Names read the conclusion left to right, hypotheses after `of`: `le_sup_left` (`a ≤ a ⊔ b`), `inv_inv` (`a⁻¹⁻¹ = a`), `le_of_lt` (`a < b → a ≤ b`).

```lean -panel -stretch
example {R : Type*} [CommRing R] (a b : R) :
    (a + b) ^ 2 = a ^ 2 + 2 * a * b + b ^ 2 := by
  ring
example {G : Type*} [Group G] (a b : G) :
    (a * b)⁻¹ * a = b⁻¹ := by
  group
```

`ring` decides identities in commutative (semi)rings, `group` in groups; `field_simp` clears denominators.

# Summary

- Orders form a chain of classes: `Preorder`, `PartialOrder`, `Lattice`, `CompleteLattice`; `Set α` is a complete lattice.
- Knaster–Tarski: a monotone map on a complete lattice has least and greatest fixed points, `OrderHom.lfp` and `OrderHom.gfp`.
- Algebra exists twice, multiplicative and additive: `Monoid`, `Group`, `Ring`, `Field` and their `Add` versions.
- Morphisms and substructures are bundled structures; `ext` proves them equal.
- Substructures form complete lattices, so the order API applies to them.
- Quotients `G ⧸ N` and `R ⧸ I` carry the structure by instance.
