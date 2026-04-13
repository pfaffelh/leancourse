import Mathlib

/-
# Exercises: Topology

These exercises cover continuity, open/closed sets, metric spaces,
and compactness. Replace each `sorry` with a proof.
-/

open Filter

/- ## Part 1: Continuous Functions -/

-- Exercise 1: The identity function is continuous
example : Continuous (id : ℝ → ℝ) := by
  sorry

-- Exercise 2: A constant function is continuous
example (c : ℝ) : Continuous (fun _ : ℝ ↦ c) := by
  sorry

-- Exercise 3: The composition of continuous functions is continuous
example {α β γ : Type*} [TopologicalSpace α] [TopologicalSpace β]
    [TopologicalSpace γ] (f : α → β) (g : β → γ)
    (hf : Continuous f) (hg : Continuous g) : Continuous (g ∘ f) := by
  sorry

-- Exercise 4: Addition is continuous on ℝ × ℝ → ℝ
example : Continuous (fun p : ℝ × ℝ ↦ p.1 + p.2) := by
  sorry

-- Exercise 5: Multiplication by a constant is continuous
example (c : ℝ) : Continuous (fun x : ℝ ↦ c * x) := by
  sorry

-- Exercise 6: The function x ↦ x^2 is continuous on ℝ
example : Continuous (fun x : ℝ ↦ x ^ 2) := by
  sorry

-- Exercise 7: The first projection is continuous
example : Continuous (Prod.fst : ℝ × ℝ → ℝ) := by
  sorry

/- ## Part 2: Open and Closed Sets -/

-- Exercise 8: The empty set is open
example : IsOpen (∅ : Set ℝ) := by
  sorry

-- Exercise 9: The whole space is open
example : IsOpen (Set.univ : Set ℝ) := by
  sorry

-- Exercise 10: The preimage of an open set under a continuous function is open
example (f : ℝ → ℝ) (hf : Continuous f) (s : Set ℝ) (hs : IsOpen s) :
    IsOpen (f ⁻¹' s) := by
  sorry

-- Exercise 11: The empty set is closed
example : IsClosed (∅ : Set ℝ) := by
  sorry

-- Exercise 12: A singleton is closed in ℝ
example (x : ℝ) : IsClosed ({x} : Set ℝ) := by
  sorry

-- Exercise 13: The union of two open sets is open
example (s t : Set ℝ) (hs : IsOpen s) (ht : IsOpen t) : IsOpen (s ∪ t) := by
  sorry

-- Exercise 14: The intersection of two open sets is open
example (s t : Set ℝ) (hs : IsOpen s) (ht : IsOpen t) : IsOpen (s ∩ t) := by
  sorry

/- ## Part 3: Metric Spaces -/

-- Exercise 15: dist x x = 0
example (x : ℝ) : dist x x = 0 := by
  sorry

-- Exercise 16: dist is symmetric
example (x y : ℝ) : dist x y = dist y x := by
  sorry

-- Exercise 17: Triangle inequality
example (x y z : ℝ) : dist x z ≤ dist x y + dist y z := by
  sorry

-- Exercise 18: dist is nonneg
example (x y : ℝ) : 0 ≤ dist x y := by
  sorry

-- Exercise 19: In a metric space, open balls are open.
example {X : Type*} [MetricSpace X] (x : X) (r : ℝ) :
    IsOpen (Metric.ball x r) := by
  sorry

/- ## Part 4: Compact Sets -/

-- Exercise 20: A closed interval is compact
example (a b : ℝ) : IsCompact (Set.Icc a b) := by
  sorry

-- Exercise 21: The image of a compact set under a continuous function is compact
example (f : ℝ → ℝ) (hf : Continuous f) (K : Set ℝ) (hK : IsCompact K) :
    IsCompact (f '' K) := by
  sorry

-- Exercise 22: A continuous function on a compact set attains its maximum.
-- Hint: IsCompact.exists_isMaxOn, or bounded/closed arguments.
example (f : ℝ → ℝ) (hf : Continuous f) (a b : ℝ) (hab : a ≤ b) :
    ∃ x ∈ Set.Icc a b, ∀ y ∈ Set.Icc a b, f y ≤ f x := by
  sorry

/- ## Part 5: Filters and Topology -/

-- Exercise 23: f is continuous iff it is continuous at every point.
example {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (f : X → Y) :
    Continuous f ↔ ∀ x, ContinuousAt f x := by
  sorry

-- Exercise 24: f is continuous at x iff Tendsto f (nhds x) (nhds (f x)).
example {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (f : X → Y)
    (x : X) : ContinuousAt f x ↔ Tendsto f (nhds x) (nhds (f x)) := by
  sorry
