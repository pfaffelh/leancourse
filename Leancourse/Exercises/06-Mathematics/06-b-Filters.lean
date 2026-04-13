import Mathlib

/-
# Exercises: Filters

These exercises cover the construction and use of filters in Mathlib,
including Filter.Tendsto, Filter.Eventually, and Filter.atTop.
Replace each `sorry` with a proof.
-/

open Filter

/- ## Part 1: Principal Filters -/

-- Exercise 1: The whole space is in any filter
example {α : Type*} (F : Filter α) : Set.univ ∈ F := by
  sorry

-- Exercise 2: A set is in the principal filter 𝓟 s iff s ⊆ it
example {α : Type*} (s t : Set α) : t ∈ 𝓟 s ↔ s ⊆ t := by
  sorry

-- Exercise 3: s is in its own principal filter
example {α : Type*} (s : Set α) : s ∈ 𝓟 s := by
  sorry

-- Exercise 4: If s ∈ F and s ⊆ t, then t ∈ F (upward closure)
example {α : Type*} (F : Filter α) (s t : Set α) (hs : s ∈ F) (hst : s ⊆ t) :
    t ∈ F := by
  sorry

-- Exercise 5: If s ∈ F and t ∈ F, then s ∩ t ∈ F
example {α : Type*} (F : Filter α) (s t : Set α) (hs : s ∈ F) (ht : t ∈ F) :
    s ∩ t ∈ F := by
  sorry

/- ## Part 2: The atTop Filter -/

-- Exercise 6: The set {n : ℕ | n ≥ 0} is in atTop
example : {n : ℕ | n ≥ 0} ∈ (atTop : Filter ℕ) := by
  sorry

-- Exercise 7: The set {n : ℕ | n ≥ 1000} is in atTop
example : {n : ℕ | n ≥ 1000} ∈ (atTop : Filter ℕ) := by
  sorry

-- Exercise 8: The set of even numbers is NOT in atTop
-- (This is harder; you may skip it)
-- Hint: show that for any N, there exists n ≥ N with n odd.
example : {n : ℕ | n % 2 = 0} ∉ (atTop : Filter ℕ) := by
  sorry

/- ## Part 3: Filter.Eventually -/

-- Exercise 9: Eventually n ≥ 100 with respect to atTop
example : ∀ᶠ n in (atTop : Filter ℕ), n ≥ 100 := by
  sorry

-- Exercise 10: If p holds eventually and q holds eventually, then p ∧ q holds eventually
example {α : Type*} {F : Filter α} {p q : α → Prop}
    (hp : ∀ᶠ x in F, p x) (hq : ∀ᶠ x in F, q x) :
    ∀ᶠ x in F, p x ∧ q x := by
  sorry

-- Exercise 11: If p implies q and p holds eventually, then q holds eventually
example {α : Type*} {F : Filter α} {p q : α → Prop}
    (hpq : ∀ x, p x → q x) (hp : ∀ᶠ x in F, p x) :
    ∀ᶠ x in F, q x := by
  sorry

-- Exercise 12: Eventually, n + 1 > n
example : ∀ᶠ n in (atTop : Filter ℕ), n + 1 > n := by
  sorry

/- ## Part 4: Filter.Tendsto -/

-- Exercise 13: The identity function tends to atTop along atTop
example : Tendsto id (atTop : Filter ℕ) atTop := by
  sorry

-- Exercise 14: The function n ↦ n + 1 tends to atTop along atTop
example : Tendsto (fun n : ℕ ↦ n + 1) atTop atTop := by
  sorry

-- Exercise 15: The function n ↦ 2 * n tends to atTop along atTop
example : Tendsto (fun n : ℕ ↦ 2 * n) atTop atTop := by
  sorry

-- Exercise 16: A constant sequence converges to that constant
example (c : ℝ) : Tendsto (fun _ : ℕ ↦ c) atTop (nhds c) := by
  sorry

-- Exercise 17: If f tends to l and g tends to m, then f + g tends to l + m
-- Hint: use Filter.Tendsto.add
example (f g : ℕ → ℝ) (l m : ℝ)
    (hf : Tendsto f atTop (nhds l)) (hg : Tendsto g atTop (nhds m)) :
    Tendsto (f + g) atTop (nhds (l + m)) := by
  sorry

/- ## Part 5: Relating Filters and Sequences -/

-- Exercise 18: A sequence converging to 0 is eventually bounded by any ε > 0
-- Hint: use Metric.tendsto_atTop
example (a : ℕ → ℝ) (ha : Tendsto a atTop (nhds 0)) (ε : ℝ) (hε : ε > 0) :
    ∀ᶠ n in atTop, |a n| < ε := by
  sorry

-- Exercise 19: Composition of Tendsto
-- If a → l along atTop and f is continuous at l, then f ∘ a → f l
example {f : ℝ → ℝ} {a : ℕ → ℝ} {l : ℝ}
    (ha : Tendsto a atTop (nhds l)) (hf : ContinuousAt f l) :
    Tendsto (f ∘ a) atTop (nhds (f l)) := by
  sorry

-- Exercise 20: The squeeze theorem for filters
-- If a ≤ b ≤ c eventually and a → l and c → l, then b → l
-- Hint: use tendsto_of_tendsto_of_tendsto_of_le_of_le
example (a b c : ℕ → ℝ) (l : ℝ)
    (ha : Tendsto a atTop (nhds l))
    (hc : Tendsto c atTop (nhds l))
    (hab : ∀ᶠ n in atTop, a n ≤ b n)
    (hbc : ∀ᶠ n in atTop, b n ≤ c n) :
    Tendsto b atTop (nhds l) := by
  sorry

/- ## Part 6: Building filters from scratch

These exercises follow the b-mehta/Buzzard pedagogy: a filter is a
"generalized subset" defined by which actual subsets contain it.
Here you construct filters by hand, verifying the three axioms
(univ_sets, sets_of_superset, inter_sets).
-/

-- Exercise 21: Construct the principal filter 𝓟 s by hand.
-- A set t is "in 𝓟 s" iff s ⊆ t.
example {α : Type*} (s : Set α) : Filter α where
  sets := {t | s ⊆ t}
  univ_sets := by sorry
  sets_of_superset := by sorry
  inter_sets := by sorry

-- Exercise 22: Construct the cofinite filter by hand.
-- Hint: compl_univ, Set.finite_empty, compl_subset_compl,
-- Set.Finite.subset, compl_inter, Set.Finite.union.
example (α : Type*) : Filter α where
  sets := {s : Set α | sᶜ.Finite}
  univ_sets := by sorry
  sets_of_superset := by sorry
  inter_sets := by sorry

-- Exercise 23: Construct atTop' on a nonempty linear order.
-- A set is "big" if it contains a tail [x, ∞).
example (L : Type*) [LinearOrder L] (e : L) : Filter L where
  sets := {X : Set L | ∃ x : L, ∀ y, x ≤ y → y ∈ X}
  univ_sets := by sorry
  sets_of_superset := by sorry
  inter_sets := by sorry

-- Exercise 24: Construct the neighborhood filter nhds' x by hand.
-- A set is a neighborhood of x if it contains an open set
-- containing x.
example {X : Type*} [TopologicalSpace X] (x : X) : Filter X where
  sets := {s : Set X | ∃ U : Set X, x ∈ U ∧ IsOpen U ∧ U ⊆ s}
  univ_sets := by sorry
  sets_of_superset := by sorry
  inter_sets := by sorry

-- Exercise 25: Construct the pushforward map' by hand.
-- Hint: a set s : Set β is in (map' m F) iff m ⁻¹' s ∈ F.
example {α β : Type*} (F : Filter α) (m : α → β) : Filter β where
  sets := {s | m ⁻¹' s ∈ F}
  univ_sets := by sorry
  sets_of_superset := by sorry
  inter_sets := by sorry

/- ## Part 7: The order on filters

Filters carry a partial order: F ≤ G means G.sets ⊆ F.sets, i.e.
"the smaller filter has more sets". This matches the generalized-subset
intuition: F ≤ G means F is contained in G as a generalized subset.
-/

-- Exercise 26: 𝓟 s ≤ 𝓟 t ↔ s ⊆ t.
example {α : Type*} (s t : Set α) : 𝓟 s ≤ 𝓟 t ↔ s ⊆ t := by
  sorry

-- Exercise 27: F ≤ 𝓟 s ↔ s ∈ F.
example {α : Type*} (F : Filter α) (s : Set α) :
    F ≤ 𝓟 s ↔ s ∈ F := by
  sorry

-- Exercise 28: ⊥ ≤ F for every filter F.
example {α : Type*} (F : Filter α) : ⊥ ≤ F := by
  sorry

-- Exercise 29: F ≤ ⊤ for every filter F.
example {α : Type*} (F : Filter α) : F ≤ ⊤ := by
  sorry

-- Exercise 30: On ℕ, the cofinite filter is ≤ atTop.
-- (Every set in atTop has finite complement.)
example : (cofinite : Filter ℕ) ≤ atTop := by
  sorry
