import VersoManual
import Manual.Meta
import Leancourse.Misc.Defs
import Mathlib

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open MyDef

set_option pp.rawOnError true
set_option verso.docstring.allowMissing true

#doc (Manual) "The Algebraic Hierarchy in Mathlib" =>
%%%
htmlSplit := .never
tag := "algebraic-hierarchy-mathlib"
%%%

One of the great achievements of Mathlib is a carefully designed hierarchy of
algebraic structures, encoded using Lean's typeclass system. In this section we
explore this hierarchy from the ground up: from basic operations to groups,
rings, fields, and their morphisms and substructures.

# Notation and naming conventions
%%%
tag := "algebra-notation"
%%%

Unicode symbols can be typed via a backslash escape (e.g. `\inv` produces
`⁻¹`).  Hover over a symbol in VS Code to see how to type it.

:::table +header
* + Symbol
  + Lean name
  + Reads as
  + Typed as
* + `*`
  + `Mul.mul a b`
  + "a times b"
  + (ASCII)
* + `+`
  + `Add.add a b`
  + "a plus b"
  + (ASCII)
* + `0`
  + `Zero.zero`
  + "zero"
  + (ASCII)
* + `1`
  + `One.one`
  + "one"
  + (ASCII)
* + `a⁻¹`
  + `Inv.inv a`
  + "a inverse"
  + `\inv` or `\-1`
* + `-a`
  + `Neg.neg a`
  + "minus a"
  + (ASCII)
* + `a / b`
  + `HDiv.hDiv a b`
  + "a divided by b"
  + (ASCII)
* + `→*`
  + `MonoidHom α β`
  + "monoid homomorphism"
  + `\to*`
* + `→+`
  + `AddMonoidHom α β`
  + "additive monoid homomorphism"
  + `\to+`
* + `→+*`
  + `RingHom α β`
  + "ring homomorphism"
  + `\to+*`
* + `R ⧸ I`
  + `HasQuotient.Quotient`
  + "R modulo I"
  + `\quot`
* + `⊥`
  + `Bot.bot`
  + "the trivial sub-object"
  + `\bot`
* + `⊤`
  + `Top.top`
  + "the whole object as a sub-object"
  + `\top`
:::

Naming hints.

- *Additive versus multiplicative.*  Mathlib systematically duplicates
  algebraic notions into an additive (`Add`, `+`, `0`, `-a`) and a
  multiplicative (`Mul`, `*`, `1`, `a⁻¹`) version.  Lemmas for the
  additive side are prefixed with `add_`: `add_assoc`, `add_comm`,
  `add_zero`, `neg_add_cancel`, etc.
- *"Class" suffix.*  `MulOneClass`, `AddZeroClass` are the bare
  algebraic laws for unit elements; they are weaker than a full monoid.
- *Bundled morphisms.*  `→*`, `→+`, `→+*` are bundled: they package a
  function together with proofs that it preserves the relevant
  operations.  Lemmas are named `map_mul`, `map_add`, `map_one`,
  `map_zero`, `map_pow`, `map_neg`.
- *Subgroups and ideals.*  `Subgroup G`, `Subring R`, `Ideal R` are
  bundled sub-objects with membership `a ∈ H`, closed under the
  relevant operations (`H.mul_mem`, `H.inv_mem`, `H.add_mem`, etc.).

# From operations to monoids
%%%
tag := "operations-to-monoids"
%%%

At the bottom of the hierarchy sit the basic operation typeclasses:
- `Mul α` provides a multiplication `*` on `α`.
- `Add α` provides an addition `+` on `α`.
- `One α` provides a distinguished element `1 : α`.
- `Zero α` provides a distinguished element `0 : α`.

These are combined step by step:
- `MulOneClass α` : a type with `*` and `1`, satisfying `1 * a = a` and `a * 1 = a`.
- `Monoid α` : a `MulOneClass` with associativity of `*`.
- `AddMonoid α` : the additive version (with `+` and `0`).
- `CommMonoid α` : a monoid where `*` is commutative.

```lean
-- ℕ is an additive commutative monoid
#check (inferInstance : AddCommMonoid ℕ)

-- Associativity is available as a lemma
example (a b c : ℕ) : a + b + c = a + (b + c) :=
  add_assoc a b c

-- The identity element
example (a : ℕ) : a + 0 = a :=
  add_zero a
```

# Groups
%%%
tag := "groups"
%%%

A *group* is a monoid where every element has an inverse.
- `Group α` : multiplicative group (inverse written `a⁻¹`, typed `\inv` or `\-1`).
- `AddGroup α` : additive group (inverse written `-a`).
- `CommGroup α`, `AddCommGroup α` : commutative (abelian) versions.

```lean
-- ℤ is an additive commutative group
#check (inferInstance : AddCommGroup ℤ)

-- Cancellation
example (a b : ℤ) : a + b - b = a := by
  omega

-- In a general group
example {G : Type*} [Group G] (a : G) : a * a⁻¹ = 1 :=
  mul_inv_cancel a

example {G : Type*} [Group G] (a b : G) :
    (a * b)⁻¹ = b⁻¹ * a⁻¹ :=
  mul_inv_rev a b
```

# Rings and fields
%%%
tag := "rings-and-fields"
%%%

A *ring* has both addition (forming an abelian group) and multiplication
(forming a monoid), linked by distributivity.

- `Ring α` : a (unital) ring.
- `CommRing α` : a commutative ring.
- `Field α` : a field (commutative ring where every nonzero element is invertible).

```lean
-- ℝ is a field, hence also a commutative ring
#check (inferInstance : Field ℝ)
#check (inferInstance : CommRing ℝ)

-- Distributivity
example (a b c : ℝ) : a * (b + c) = a * b + a * c :=
  mul_add a b c

-- Division in a field
example (a : ℝ) (ha : a ≠ 0) : a * a⁻¹ = 1 :=
  mul_inv_cancel₀ ha
```

Mathlib also provides ordered variants:
- `OrderedRing α` : a ring with a compatible order.
- `LinearOrderedField α` : a linearly ordered field (like `ℝ` or `ℚ`).

```lean
#check (inferInstance : LinearOrder ℝ)
#check (inferInstance : IsStrictOrderedRing ℝ)
```

# Morphisms
%%%
tag := "morphisms"
%%%

Algebraic morphisms are functions that preserve the relevant structure.
Mathlib uses bundled morphisms (structures carrying both the function and the
proof of preservation).

- `MonoidHom` (notation `→*`) : maps preserving `*` and `1`.
- `AddMonoidHom` (notation `→+`) : maps preserving `+` and `0`.
- `RingHom` (notation `→+*`) : maps preserving both `+`, `*`, `0`, `1`.

```lean
-- The inclusion ℤ → ℚ is a ring homomorphism
#check (Int.castRingHom ℚ : ℤ →+* ℚ)

-- A ring homomorphism preserves addition
example (f : ℤ →+* ℚ) (a b : ℤ) : f (a + b) = f a + f b :=
  f.map_add a b

-- A ring homomorphism preserves multiplication
example (f : ℤ →+* ℚ) (a b : ℤ) : f (a * b) = f a * f b :=
  f.map_mul a b

-- A ring homomorphism maps 0 to 0
example (f : ℤ →+* ℚ) : f 0 = 0 :=
  f.map_zero
```

# Substructures
%%%
tag := "substructures"
%%%

Mathlib provides types for substructures of algebraic objects:
- `Subgroup G` : a subgroup of `G`.
- `Subring R` : a subring of `R`.
- `Subalgebra R A` : a subalgebra of `A` over `R`.
- `Ideal R` : an ideal of a (commutative) ring `R`.

These are *bundled*: a `Subgroup G` consists of a carrier set together with
proofs that it is closed under the group operations.

```lean
-- The trivial subgroup (just the identity)
example {G : Type*} [Group G] : Subgroup G :=
  ⊥

-- The whole group as a subgroup
example {G : Type*} [Group G] : Subgroup G :=
  ⊤

-- Membership
example {G : Type*} [Group G] (H : Subgroup G) (a b : G)
    (ha : a ∈ H) (hb : b ∈ H) : a * b ∈ H :=
  H.mul_mem ha hb

-- Subgroups form a complete lattice
#check (inferInstance : CompleteLattice (AddSubgroup ℤ))
```

# Quotient structures
%%%
tag := "quotients"
%%%

Given a normal subgroup `N` of a group `G`, the quotient `G ⧸ N` is again a
group. Similarly, given an ideal `I` of a ring `R`, the quotient `R ⧸ I` is a
ring.

```lean
-- The quotient of a commutative ring by an ideal
example (R : Type*) [CommRing R] (I : Ideal R) : CommRing (R ⧸ I) :=
  inferInstance
```

The quotient map is a ring homomorphism:

{docstring Ideal.Quotient.mk}

# The ext tactic for algebraic structures
%%%
tag := "ext-algebraic"
%%%

The `ext` tactic is very useful when proving equalities between algebraic
objects. For instance, two subgroups are equal if they have the same elements;
two morphisms are equal if they agree on all inputs.

```lean
-- Two subgroups with the same carrier are equal
example {G : Type*} [Group G] (H K : Subgroup G) (h : ∀ g, g ∈ H ↔ g ∈ K) :
    H = K := by
  ext g
  exact h g

-- Two ring homomorphisms agreeing on all elements are equal
example {R S : Type*} [Ring R] [Ring S] (f g : R →+* S) (h : ∀ r, f r = g r) :
    f = g := by
  ext r
  exact h r
```

# Navigating the hierarchy
%%%
tag := "navigating-hierarchy"
%%%

When working with Mathlib's algebraic hierarchy, recall the
exploration commands introduced in the Lean chapter: `#check` for
types, `#print` for definitions and fields of typeclasses,
`inferInstance` for checking whether a given instance exists, and
`exact?` / `apply?` for lemma search.  In addition:

- Look at `Mathlib.Algebra` and `Mathlib.GroupTheory` for the files
  relevant to the structure you are working with.
- Lemma names follow the predictable pattern `<operation>_<result>`,
  e.g. `mul_assoc`, `add_comm`, `map_mul`, `inv_inv`.

```lean
-- Check what instances ℝ has
#check (inferInstance : Field ℝ)
#check (inferInstance : LinearOrder ℝ)
#check (inferInstance : AddCommGroup ℝ)

-- A general proof that works for any commutative ring
example {R : Type*} [CommRing R] (a b : R) : (a + b) ^ 2 = a ^ 2 + 2 * a * b + b ^ 2 := by
  ring
```

The `ring` tactic is a powerful decision procedure that closes goals that are
identities in commutative (semi)rings. Similarly, `group` works for group
identities, and `field_simp` helps simplify field expressions involving
division.
