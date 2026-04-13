import Mathlib

/-
# Exercises: The Algebraic Hierarchy

These exercises cover monoids, groups, rings, fields, morphisms,
substructures, and quotients. Replace each `sorry` with a proof.
-/

/- ## Part 1: Monoids and additive monoids -/

-- Exercise 1: a + 0 = a in ℕ.
example (a : ℕ) : a + 0 = a := by
  sorry

-- Exercise 2: associativity of addition on ℕ.
example (a b c : ℕ) : a + b + c = a + (b + c) := by
  sorry

-- Exercise 3: In a general monoid, 1 * a = a.
example {M : Type*} [Monoid M] (a : M) : 1 * a = a := by
  sorry

-- Exercise 4: In a commutative monoid, (a * b) * c = a * (b * c).
example {M : Type*} [CommMonoid M] (a b c : M) :
    a * b * c = a * (b * c) := by
  sorry

/- ## Part 2: Groups -/

-- Exercise 5: In a group, a * a⁻¹ = 1.
example {G : Type*} [Group G] (a : G) : a * a⁻¹ = 1 := by
  sorry

-- Exercise 6: In a group, (a * b)⁻¹ = b⁻¹ * a⁻¹.
example {G : Type*} [Group G] (a b : G) : (a * b)⁻¹ = b⁻¹ * a⁻¹ := by
  sorry

-- Exercise 7: In a group, left cancellation: a * b = a * c → b = c.
example {G : Type*} [Group G] (a b c : G) (h : a * b = a * c) : b = c := by
  sorry

-- Exercise 8: In an abelian (commutative) group, (a + b) - a = b.
example {G : Type*} [AddCommGroup G] (a b : G) : (a + b) - a = b := by
  sorry

-- Exercise 9: Inverse is unique: if a * b = 1 then b = a⁻¹.
example {G : Type*} [Group G] (a b : G) (h : a * b = 1) : b = a⁻¹ := by
  sorry

/- ## Part 3: Rings -/

-- Exercise 10: In any ring, 0 * a = 0.
example {R : Type*} [Ring R] (a : R) : 0 * a = 0 := by
  sorry

-- Exercise 11: In any ring, (-a) * b = -(a * b).
example {R : Type*} [Ring R] (a b : R) : (-a) * b = -(a * b) := by
  sorry

-- Exercise 12: Distributivity from the right.
example {R : Type*} [Ring R] (a b c : R) :
    (a + b) * c = a * c + b * c := by
  sorry

-- Exercise 13: Binomial identity in a commutative ring.
example {R : Type*} [CommRing R] (a b : R) :
    (a + b) ^ 2 = a ^ 2 + 2 * a * b + b ^ 2 := by
  sorry

-- Exercise 14: Difference of squares.
example {R : Type*} [CommRing R] (a b : R) :
    (a + b) * (a - b) = a ^ 2 - b ^ 2 := by
  sorry

/- ## Part 4: Fields -/

-- Exercise 15: In a field, a ≠ 0 → a * a⁻¹ = 1.
example {K : Type*} [Field K] (a : K) (ha : a ≠ 0) : a * a⁻¹ = 1 := by
  sorry

-- Exercise 16: In a field, a nonzero element has a unique inverse.
example {K : Type*} [Field K] (a b : K) (ha : a ≠ 0) (h : a * b = 1) :
    b = a⁻¹ := by
  sorry

-- Exercise 17: (a / b) * b = a when b ≠ 0.
example {K : Type*} [Field K] (a b : K) (hb : b ≠ 0) : (a / b) * b = a := by
  sorry

/- ## Part 5: Morphisms -/

-- Exercise 18: A ring hom preserves addition.
example {R S : Type*} [Ring R] [Ring S] (f : R →+* S) (a b : R) :
    f (a + b) = f a + f b := by
  sorry

-- Exercise 19: A ring hom preserves 0.
example {R S : Type*} [Ring R] [Ring S] (f : R →+* S) : f 0 = 0 := by
  sorry

-- Exercise 20: A monoid hom preserves powers.
example {M N : Type*} [Monoid M] [Monoid N] (f : M →* N) (a : M) (n : ℕ) :
    f (a ^ n) = (f a) ^ n := by
  sorry

-- Exercise 21: Two ring homs that agree on every element are equal.
example {R S : Type*} [Ring R] [Ring S] (f g : R →+* S)
    (h : ∀ r, f r = g r) : f = g := by
  sorry

/- ## Part 6: Substructures -/

-- Exercise 22: The trivial subgroup contains only 1.
example {G : Type*} [Group G] (a : G) (ha : a ∈ (⊥ : Subgroup G)) : a = 1 := by
  sorry

-- Exercise 23: Every element is in the top subgroup.
example {G : Type*} [Group G] (a : G) : a ∈ (⊤ : Subgroup G) := by
  sorry

-- Exercise 24: A subgroup is closed under multiplication.
example {G : Type*} [Group G] (H : Subgroup G) (a b : G)
    (ha : a ∈ H) (hb : b ∈ H) : a * b ∈ H := by
  sorry

-- Exercise 25: A subgroup is closed under inverse.
example {G : Type*} [Group G] (H : Subgroup G) (a : G) (ha : a ∈ H) :
    a⁻¹ ∈ H := by
  sorry

-- Exercise 26: Two subgroups with the same elements are equal.
example {G : Type*} [Group G] (H K : Subgroup G)
    (h : ∀ g, g ∈ H ↔ g ∈ K) : H = K := by
  sorry

/- ## Part 7: Quotients -/

-- Exercise 27: In R ⧸ I, the image of r ∈ I is zero.
example {R : Type*} [CommRing R] (I : Ideal R) (r : R) (hr : r ∈ I) :
    (Ideal.Quotient.mk I) r = 0 := by
  sorry

-- Exercise 28: The quotient map is a ring hom, hence preserves multiplication.
example {R : Type*} [CommRing R] (I : Ideal R) (a b : R) :
    (Ideal.Quotient.mk I) (a * b) =
      (Ideal.Quotient.mk I) a * (Ideal.Quotient.mk I) b := by
  sorry
