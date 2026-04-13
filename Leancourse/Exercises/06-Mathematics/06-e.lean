import Mathlib

/-
# Exercises: Measure Theory

These exercises cover measurable spaces, measurable functions, measures,
and probability measures. Replace each `sorry` with a proof.
-/

open MeasureTheory

/- ## Part 1: Measurable Sets -/

-- Exercise 1: The empty set is measurable.
example {α : Type*} [MeasurableSpace α] : MeasurableSet (∅ : Set α) := by
  sorry

-- Exercise 2: The whole space is measurable.
example {α : Type*} [MeasurableSpace α] : MeasurableSet (Set.univ : Set α) := by
  sorry

-- Exercise 3: The complement of a measurable set is measurable.
example {α : Type*} [MeasurableSpace α] (s : Set α) (hs : MeasurableSet s) :
    MeasurableSet sᶜ := by
  sorry

-- Exercise 4: The union of two measurable sets is measurable.
example {α : Type*} [MeasurableSpace α] (s t : Set α)
    (hs : MeasurableSet s) (ht : MeasurableSet t) :
    MeasurableSet (s ∪ t) := by
  sorry

-- Exercise 5: The intersection of two measurable sets is measurable.
example {α : Type*} [MeasurableSpace α] (s t : Set α)
    (hs : MeasurableSet s) (ht : MeasurableSet t) :
    MeasurableSet (s ∩ t) := by
  sorry

-- Exercise 6: A countable union of measurable sets is measurable.
example {α : Type*} [MeasurableSpace α] (s : ℕ → Set α)
    (hs : ∀ n, MeasurableSet (s n)) :
    MeasurableSet (⋃ n, s n) := by
  sorry

/- ## Part 2: Measurable Functions -/

-- Exercise 7: The identity is measurable.
example : Measurable (id : ℝ → ℝ) := by
  sorry

-- Exercise 8: A constant function is measurable.
example (c : ℝ) : Measurable (fun _ : ℝ ↦ c) := by
  sorry

-- Exercise 9: Composition of measurable functions is measurable.
example {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSpace γ] (f : α → β) (g : β → γ)
    (hf : Measurable f) (hg : Measurable g) : Measurable (g ∘ f) := by
  sorry

-- Exercise 10: A continuous function ℝ → ℝ is measurable.
example (f : ℝ → ℝ) (hf : Continuous f) : Measurable f := by
  sorry

-- Exercise 11: The sum of two measurable functions is measurable.
example (f g : ℝ → ℝ) (hf : Measurable f) (hg : Measurable g) :
    Measurable (fun x ↦ f x + g x) := by
  sorry

/- ## Part 3: Measures -/

-- Exercise 12: The measure of the empty set is 0.
example {α : Type*} [MeasurableSpace α] (μ : Measure α) : μ ∅ = 0 := by
  sorry

-- Exercise 13: Monotonicity of measures.
example {α : Type*} [MeasurableSpace α] (μ : Measure α) (s t : Set α)
    (hst : s ⊆ t) : μ s ≤ μ t := by
  sorry

-- Exercise 14: Countable subadditivity.
example {α : Type*} [MeasurableSpace α] (μ : Measure α) (s : ℕ → Set α) :
    μ (⋃ n, s n) ≤ ∑' n, μ (s n) := by
  sorry

-- Exercise 15: The Lebesgue measure of a point is 0.
-- Hint: Real.volume_singleton
example (x : ℝ) : volume ({x} : Set ℝ) = 0 := by
  sorry

-- Exercise 16: The Lebesgue measure of a closed interval.
-- Hint: Real.volume_Icc
example (a b : ℝ) (hab : a ≤ b) :
    volume (Set.Icc a b) = ENNReal.ofReal (b - a) := by
  sorry

/- ## Part 4: Probability Measures -/

-- Exercise 17: A probability measure assigns 1 to the whole space.
example {α : Type*} [MeasurableSpace α] (μ : Measure α)
    [IsProbabilityMeasure μ] : μ Set.univ = 1 := by
  sorry

-- Exercise 18: Any set has measure ≤ 1 under a probability measure.
example {α : Type*} [MeasurableSpace α] (μ : Measure α)
    [IsProbabilityMeasure μ] (s : Set α) : μ s ≤ 1 := by
  sorry

-- Exercise 19: Under a finite measure, a set of full measure has null complement.
example {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]
    (s : Set α) (hs : MeasurableSet s) (hfull : μ s = μ Set.univ) :
    μ sᶜ = 0 := by
  sorry

-- Exercise 20: For a probability measure, μ sᶜ = 1 - μ s when s is measurable.
example {α : Type*} [MeasurableSpace α] (μ : Measure α)
    [IsProbabilityMeasure μ] (s : Set α) (hs : MeasurableSet s) :
    μ sᶜ = 1 - μ s := by
  sorry

/- ## Part 5: Almost Everywhere -/

-- Exercise 21: A property holding everywhere holds almost everywhere.
example {α : Type*} [MeasurableSpace α] (μ : Measure α) (p : α → Prop)
    (hp : ∀ x, p x) : ∀ᵐ x ∂μ, p x := by
  sorry

-- Exercise 22: If p and q hold a.e., then p ∧ q holds a.e.
example {α : Type*} [MeasurableSpace α] (μ : Measure α) (p q : α → Prop)
    (hp : ∀ᵐ x ∂μ, p x) (hq : ∀ᵐ x ∂μ, q x) :
    ∀ᵐ x ∂μ, p x ∧ q x := by
  sorry
