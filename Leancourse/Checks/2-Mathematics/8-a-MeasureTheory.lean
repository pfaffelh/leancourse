import Mathlib

/-
# (witness) 2.8-a -- Measure theory

*Notes chapter 2.8, week 14.*

These exercises cover measurable spaces, measurable functions, measures,
and probability measures. Replace each `sorry` with a proof.
-/

open MeasureTheory

/- ## Part 1: Measurable Sets -/

-- Exercise 1: The empty set is measurable.
example {α : Type*} [MeasurableSpace α] : MeasurableSet (∅ : Set α) := by
  exact MeasurableSet.empty

-- Exercise 2: The whole space is measurable.
example {α : Type*} [MeasurableSpace α] : MeasurableSet (Set.univ : Set α) := by
  exact MeasurableSet.univ

-- Exercise 3: The complement of a measurable set is measurable.
example {α : Type*} [MeasurableSpace α] (s : Set α) (hs : MeasurableSet s) :
    MeasurableSet sᶜ := by
  exact hs.compl

-- Exercise 4: The union of two measurable sets is measurable.
example {α : Type*} [MeasurableSpace α] (s t : Set α)
    (hs : MeasurableSet s) (ht : MeasurableSet t) :
    MeasurableSet (s ∪ t) := by
  exact hs.union ht

-- Exercise 5: The intersection of two measurable sets is measurable.
example {α : Type*} [MeasurableSpace α] (s t : Set α)
    (hs : MeasurableSet s) (ht : MeasurableSet t) :
    MeasurableSet (s ∩ t) := by
  exact hs.inter ht

-- Exercise 6: A countable union of measurable sets is measurable.
example {α : Type*} [MeasurableSpace α] (s : ℕ → Set α)
    (hs : ∀ n, MeasurableSet (s n)) :
    MeasurableSet (⋃ n, s n) := by
  exact MeasurableSet.iUnion hs

/- ## Part 2: Measurable Functions

`fun_prop`, which sheet `2.7-a` used for continuity, works here too:
measurability is one of the properties it knows. It will not do the
structural exercises below, but it closes any goal about a concrete
expression. -/

example : Measurable fun x : ℝ ↦ Real.exp x + x ^ 2 := by
  fun_prop

-- Exercise 7: The identity is measurable.
example : Measurable (id : ℝ → ℝ) := by
  exact measurable_id

-- Exercise 8: A constant function is measurable.
example (c : ℝ) : Measurable (fun _ : ℝ ↦ c) := by
  exact measurable_const

-- Exercise 9: Composition of measurable functions is measurable.
example {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSpace γ] (f : α → β) (g : β → γ)
    (hf : Measurable f) (hg : Measurable g) : Measurable (g ∘ f) := by
  exact hg.comp hf

-- Exercise 10: A continuous function ℝ → ℝ is measurable.
example (f : ℝ → ℝ) (hf : Continuous f) : Measurable f := by
  exact hf.measurable

-- Exercise 11: The sum of two measurable functions is measurable.
example (f g : ℝ → ℝ) (hf : Measurable f) (hg : Measurable g) :
    Measurable (fun x ↦ f x + g x) := by
  exact hf.add hg

/- ## Part 3: Measures -/

-- Exercise 12: The measure of the empty set is 0.
example {α : Type*} [MeasurableSpace α] (μ : Measure α) : μ ∅ = 0 := by
  exact measure_empty

-- Exercise 13: Monotonicity of measures.
example {α : Type*} [MeasurableSpace α] (μ : Measure α) (s t : Set α)
    (hst : s ⊆ t) : μ s ≤ μ t := by
  exact measure_mono hst

-- Exercise 14: Countable subadditivity.
example {α : Type*} [MeasurableSpace α] (μ : Measure α) (s : ℕ → Set α) :
    μ (⋃ n, s n) ≤ ∑' n, μ (s n) := by
  exact measure_iUnion_le s

-- Exercise 15: The Lebesgue measure of a point is 0.
-- Hint: Real.volume_singleton
example (x : ℝ) : volume ({x} : Set ℝ) = 0 := by
  exact Real.volume_singleton

-- Exercise 16: The Lebesgue measure of a closed interval.
-- Hint: Real.volume_Icc
example (a b : ℝ) (_hab : a ≤ b) :
    volume (Set.Icc a b) = ENNReal.ofReal (b - a) := by
  rw [Real.volume_Icc]

/- ## Part 4: Probability Measures -/

-- Exercise 17: A probability measure assigns 1 to the whole space.
example {α : Type*} [MeasurableSpace α] (μ : Measure α)
    [IsProbabilityMeasure μ] : μ Set.univ = 1 := by
  exact measure_univ

-- Exercise 18: Any set has measure ≤ 1 under a probability measure.
example {α : Type*} [MeasurableSpace α] (μ : Measure α)
    [IsProbabilityMeasure μ] (s : Set α) : μ s ≤ 1 := by
  exact prob_le_one

-- Exercise 19: Under a finite measure, a set of full measure has null complement.
example {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]
    (s : Set α) (hs : MeasurableSet s) (hfull : μ s = μ Set.univ) :
    μ sᶜ = 0 := by
  rw [measure_compl hs (measure_ne_top μ s), hfull, tsub_self]

-- Exercise 20: For a probability measure, μ sᶜ = 1 - μ s when s is measurable.
example {α : Type*} [MeasurableSpace α] (μ : Measure α)
    [IsProbabilityMeasure μ] (s : Set α) (hs : MeasurableSet s) :
    μ sᶜ = 1 - μ s := by
  rw [prob_compl_eq_one_sub hs]

/- ## Part 5: Almost Everywhere -/

-- Exercise 21: A property holding everywhere holds almost everywhere.
example {α : Type*} [MeasurableSpace α] (μ : Measure α) (p : α → Prop)
    (hp : ∀ x, p x) : ∀ᵐ x ∂μ, p x := by
  exact Filter.Eventually.of_forall hp

-- Exercise 22: If p and q hold a.e., then p ∧ q holds a.e.
example {α : Type*} [MeasurableSpace α] (μ : Measure α) (p q : α → Prop)
    (hp : ∀ᵐ x ∂μ, p x) (hq : ∀ᵐ x ∂μ, q x) :
    ∀ᵐ x ∂μ, p x ∧ q x := by
  exact hp.and hq
