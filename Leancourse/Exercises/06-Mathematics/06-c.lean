import Mathlib

/-
# Exercises: Topology and Measure Theory

These exercises cover continuity, topological properties, measurable functions,
and basic measure theory. Replace each `sorry` with a proof.
-/

open Filter MeasureTheory

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

/- ## Part 3: Metric Spaces -/

-- Exercise 13: dist x x = 0
example (x : ℝ) : dist x x = 0 := by
  sorry

-- Exercise 14: dist is symmetric
example (x y : ℝ) : dist x y = dist y x := by
  sorry

-- Exercise 15: Triangle inequality
example (x y z : ℝ) : dist x z ≤ dist x y + dist y z := by
  sorry

-- Exercise 16: dist is nonneg
example (x y : ℝ) : 0 ≤ dist x y := by
  sorry

/- ## Part 4: Compact Sets -/

-- Exercise 17: A closed interval is compact
example (a b : ℝ) : IsCompact (Set.Icc a b) := by
  sorry

-- Exercise 18: The image of a compact set under a continuous function is compact
example (f : ℝ → ℝ) (hf : Continuous f) (K : Set ℝ) (hK : IsCompact K) :
    IsCompact (f '' K) := by
  sorry

/- ## Part 5: Measurable Functions -/

-- Exercise 19: The identity is measurable
example : Measurable (id : ℝ → ℝ) := by
  sorry

-- Exercise 20: A constant function is measurable
example (c : ℝ) : Measurable (fun _ : ℝ ↦ c) := by
  sorry

-- Exercise 21: Composition of measurable functions is measurable
example {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSpace γ] (f : α → β) (g : β → γ)
    (hf : Measurable f) (hg : Measurable g) : Measurable (g ∘ f) := by
  sorry

-- Exercise 22: A continuous function (ℝ → ℝ) is measurable
example (f : ℝ → ℝ) (hf : Continuous f) : Measurable f := by
  sorry

/- ## Part 6: Measures -/

-- Exercise 23: The measure of the empty set is 0
example (μ : Measure ℝ) : μ ∅ = 0 := by
  sorry

-- Exercise 24: Monotonicity of measures
example (μ : Measure ℝ) (s t : Set ℝ) (hst : s ⊆ t) : μ s ≤ μ t := by
  sorry

-- Exercise 25: The Lebesgue measure of a point is 0
-- Hint: use Real.volume_singleton
example (x : ℝ) : volume ({x} : Set ℝ) = 0 := by
  sorry

/- ## Part 7: Probability Measures -/

-- Exercise 26: If μ is a probability measure, then μ(Set.univ) = 1
example {α : Type*} [MeasurableSpace α] (μ : Measure α)
    [IsProbabilityMeasure μ] : μ Set.univ = 1 := by
  sorry

-- Exercise 27: If μ is a probability measure and s is measurable, then μ(s) ≤ 1
example {α : Type*} [MeasurableSpace α] (μ : Measure α)
    [IsProbabilityMeasure μ] (s : Set α) : μ s ≤ 1 := by
  sorry

-- Exercise 28: The complement of a set of full measure has measure 0
-- (under a finite measure)
example {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]
    (s : Set α) (hs : MeasurableSet s) (hfull : μ s = μ Set.univ) :
    μ sᶜ = 0 := by
  sorry
