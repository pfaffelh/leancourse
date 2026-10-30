import Mathlib

/-
# 2.8-a -- Measure theory

*Notes chapter 2.8, extra sheet, not lectured.*

These exercises cover measurable spaces, measurable functions, measures,
probability measures, integration and the convergence theorems.
Replace each `sorry` with a proof.
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

/- ## Part 2: Measurable Functions

`fun_prop`, which sheet `2.7-a` used for continuity, works here too:
measurability is one of the properties it knows. It will not do the
structural exercises below, but it closes any goal about a concrete
expression. -/

example : Measurable fun x : ℝ ↦ Real.exp x + x ^ 2 := by
  fun_prop

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
example (a b : ℝ) (_hab : a ≤ b) :
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

/- ## Part 6: Integration

See the sections *Integration* and *Convergence theorems* of chapter
2.8. `∫ x, f x ∂μ` is the integral of `f : α → ℝ`, `∫⁻ x, f x ∂μ` the
integral of `f : α → ℝ≥0∞`, and `∫ x in a..b, f x` the integral over
the interval from `a` to `b` with respect to Lebesgue measure. Most
statements about `∫` need `Integrable f μ`: without it, Mathlib sets
the integral to `0`. -/

-- Exercise 23: The integral of the identity. `simp` knows `integral_id`.
example : ∫ x in (0 : ℝ)..1, x = 1 / 2 := by
  sorry

-- Exercise 24: Use `integral_pow`, then compute.
example : ∫ x in (0 : ℝ)..2, x ^ 2 = 8 / 3 := by
  sorry

-- Exercise 25: The integral of a constant against a probability measure.
example {α : Type*} [MeasurableSpace α] (μ : Measure α)
    [IsProbabilityMeasure μ] (c : ℝ) : ∫ _x, c ∂μ = c := by
  sorry

-- Exercise 26: Linearity. Hint: `integral_add`.
example {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (f g : α → ℝ) (hf : Integrable f μ) (hg : Integrable g μ) :
    ∫ x, (f x + g x) ∂μ = ∫ x, f x ∂μ + ∫ x, g x ∂μ := by
  sorry

-- Exercise 27: Monotonicity.
example {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (f g : α → ℝ) (hf : Integrable f μ) (hg : Integrable g μ)
    (h : ∀ x, f x ≤ g x) : ∫ x, f x ∂μ ≤ ∫ x, g x ∂μ := by
  sorry

-- Exercise 28: A nonnegative function has a nonnegative integral. No
-- integrability is needed here. Why?
example {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (f : α → ℝ) (h : ∀ x, 0 ≤ f x) : 0 ≤ ∫ x, f x ∂μ := by
  sorry

-- Exercise 29: The integral of an indicator function is the measure of
-- the set.
example {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (s : Set α) (hs : MeasurableSet s) :
    ∫⁻ x, s.indicator 1 x ∂μ = μ s := by
  sorry

-- Exercise 30: Functions that agree almost everywhere have the same
-- integral.
example {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (f g : α → ℝ) (h : f =ᵐ[μ] g) :
    ∫ x, f x ∂μ = ∫ x, g x ∂μ := by
  sorry

/- ## Part 7: Convergence theorems

Each theorem is one lemma in Mathlib. The point of the exercises is
to read the hypotheses: which ones are there, and in which form. -/

-- Exercise 31: Monotone convergence.
example {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (f : ℕ → α → ENNReal) (hf : ∀ n, Measurable (f n))
    (hmono : Monotone f) :
    ∫⁻ x, ⨆ n, f n x ∂μ = ⨆ n, ∫⁻ x, f n x ∂μ := by
  sorry

-- Exercise 32: Fatou's lemma. Hint: `lintegral_liminf_le`.
example {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (f : ℕ → α → ENNReal) (hf : ∀ n, Measurable (f n)) :
    ∫⁻ x, Filter.liminf (fun n ↦ f n x) Filter.atTop ∂μ
      ≤ Filter.liminf (fun n ↦ ∫⁻ x, f n x ∂μ) Filter.atTop := by
  sorry

-- Exercise 33: Dominated convergence. `AEStronglyMeasurable` is the
-- measurability condition the Bochner integral uses.
example {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (f : ℕ → α → ℝ) (F g : α → ℝ)
    (hf : ∀ n, AEStronglyMeasurable (f n) μ)
    (hg : Integrable g μ)
    (hbound : ∀ n, ∀ᵐ x ∂μ, ‖f n x‖ ≤ g x)
    (hlim : ∀ᵐ x ∂μ,
      Filter.Tendsto (fun n ↦ f n x) Filter.atTop (nhds (F x))) :
    Filter.Tendsto (fun n ↦ ∫ x, f n x ∂μ) Filter.atTop
      (nhds (∫ x, F x ∂μ)) := by
  sorry
