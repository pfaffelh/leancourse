import Mathlib

/-
# 2.5-a -- The algebraic hierarchy

*Notes chapter 2.5, week 13.*

These exercises cover groups, rings, fields, morphisms,
substructures, and quotients. Replace each `sorry` with a proof.

## Tactics from earlier sheets

| sheet   | tactics  |
|---------|----------|
| `L-a`   | `exact`  |
| `1.1-b` | `decide` |
| `1.1-c` | `ring`   |
| `L-g`   | `simpa`  |
-/

/- ## Part 1: Groups -/

-- Exercise 1: In a group, (a * b)⁻¹ = b⁻¹ * a⁻¹.
example {G : Type*} [Group G] (a b : G) : (a * b)⁻¹ = b⁻¹ * a⁻¹ := by
  sorry

-- Exercise 2: In a group, left cancellation: a * b = a * c → b = c.
example {G : Type*} [Group G] (a b c : G) (h : a * b = a * c) : b = c := by
  sorry

-- Exercise 3: In an abelian (commutative) group, (a + b) - a = b.
example {G : Type*} [AddCommGroup G] (a b : G) : (a + b) - a = b := by
  sorry

-- Exercise 4: Inverse is unique: if a * b = 1 then b = a⁻¹.
example {G : Type*} [Group G] (a b : G) (h : a * b = 1) : b = a⁻¹ := by
  sorry

/- ## Part 2: Rings -/

-- Exercise 5: In any ring, (-a) * b = -(a * b).
example {R : Type*} [Ring R] (a b : R) : (-a) * b = -(a * b) := by
  sorry

-- Exercise 6: Difference of squares.
example {R : Type*} [CommRing R] (a b : R) :
    (a + b) * (a - b) = a ^ 2 - b ^ 2 := by
  sorry

/- ## Part 3: Fields -/

-- Exercise 7: In a field, a ≠ 0 → a * a⁻¹ = 1.
example {K : Type*} [Field K] (a : K) (ha : a ≠ 0) : a * a⁻¹ = 1 := by
  sorry

-- Exercise 8: In a field, a nonzero element has a unique inverse.
example {K : Type*} [Field K] (a b : K) (ha : a ≠ 0) (h : a * b = 1) :
    b = a⁻¹ := by
  sorry

-- Exercise 9: (a / b) * b = a when b ≠ 0.
example {K : Type*} [Field K] (a b : K) (hb : b ≠ 0) : (a / b) * b = a := by
  sorry

/- ## Part 4: Morphisms -/

-- Exercise 10: A ring hom preserves addition.
example {R S : Type*} [Ring R] [Ring S] (f : R →+* S) (a b : R) :
    f (a + b) = f a + f b := by
  sorry

-- Exercise 11: A ring hom preserves 0.
example {R S : Type*} [Ring R] [Ring S] (f : R →+* S) : f 0 = 0 := by
  sorry

-- Exercise 12: A monoid hom preserves powers.
example {M N : Type*} [Monoid M] [Monoid N] (f : M →* N) (a : M) (n : ℕ) :
    f (a ^ n) = (f a) ^ n := by
  sorry

-- Exercise 13: Two ring homs that agree on every element are equal.
example {R S : Type*} [Ring R] [Ring S] (f g : R →+* S)
    (h : ∀ r, f r = g r) : f = g := by
  sorry

/- ## Part 5: Substructures -/

-- Exercise 14: The trivial subgroup contains only 1.
example {G : Type*} [Group G] (a : G) (ha : a ∈ (⊥ : Subgroup G)) : a = 1 := by
  sorry

-- Exercise 15: Every element is in the top subgroup.
example {G : Type*} [Group G] (a : G) : a ∈ (⊤ : Subgroup G) := by
  sorry

-- Exercise 16: A subgroup is closed under multiplication.
example {G : Type*} [Group G] (H : Subgroup G) (a b : G)
    (ha : a ∈ H) (hb : b ∈ H) : a * b ∈ H := by
  sorry

-- Exercise 17: A subgroup is closed under inverse.
example {G : Type*} [Group G] (H : Subgroup G) (a : G) (ha : a ∈ H) :
    a⁻¹ ∈ H := by
  sorry

-- Exercise 18: Two subgroups with the same elements are equal.
example {G : Type*} [Group G] (H K : Subgroup G)
    (h : ∀ g, g ∈ H ↔ g ∈ K) : H = K := by
  sorry

/- ## Part 6: Quotients -/

-- Exercise 19: In R ⧸ I, the image of r ∈ I is zero.
example {R : Type*} [CommRing R] (I : Ideal R) (r : R) (hr : r ∈ I) :
    (Ideal.Quotient.mk I) r = 0 := by
  sorry

-- Exercise 20: The quotient map is a ring hom, hence preserves multiplication.
example {R : Type*} [CommRing R] (I : Ideal R) (a b : R) :
    (Ideal.Quotient.mk I) (a * b) =
      (Ideal.Quotient.mk I) a * (Ideal.Quotient.mk I) b := by
  sorry

/- ## Part 7: *Extra:* `ZMod` and `ℤ` -/

-- Exercise 21: The inverse of `3` in `ZMod 7`, by computation.
example : (3 : ZMod 7) * 5 = 1 := by
  sorry

-- Exercise 22: A ring morphism out of `ℤ` is unique: it sends `n` to
-- the cast of `n`.
example (R : Type*) [Ring R] (f : ℤ →+* R) (n : ℤ) : f n = n := by
  sorry
