import Mathlib

/-
# (witness) 2.7-a -- Topology

*Notes chapter 2.7, week 13.*

These exercises cover continuity, open/closed sets, metric spaces,
and compactness. Replace each `sorry` with a proof.
-/

open Filter

/- ## Part 1: Continuous Functions

Most continuity goals in Mathlib are built from continuous pieces by
composition, sums and products. `fun_prop` does exactly that search:
it takes the function apart and discharges each piece from the
registered lemmas. Try it first on every exercise of this part. -/

example : Continuous fun x : ℝ ↦ Real.exp (x ^ 2 + 3 * x) := by
  fun_prop

-- Exercise 1: `fun_prop` also uses continuity hypotheses in context.
example (f : ℝ → ℝ) (hf : Continuous f) :
    Continuous fun x ↦ f (x ^ 2) + Real.cos x := by
  fun_prop

-- Exercise 2: The identity function is continuous
example : Continuous (id : ℝ → ℝ) := by
  exact continuous_id

-- Exercise 3: A constant function is continuous
example (c : ℝ) : Continuous (fun _ : ℝ ↦ c) := by
  exact continuous_const

-- Exercise 4: The composition of continuous functions is continuous
example {α β γ : Type*} [TopologicalSpace α] [TopologicalSpace β]
    [TopologicalSpace γ] (f : α → β) (g : β → γ)
    (hf : Continuous f) (hg : Continuous g) : Continuous (g ∘ f) := by
  exact hg.comp hf

-- Exercise 5: Addition is continuous on ℝ × ℝ → ℝ
example : Continuous (fun p : ℝ × ℝ ↦ p.1 + p.2) := by
  exact continuous_add

-- Exercise 6: Multiplication by a constant is continuous
example (c : ℝ) : Continuous (fun x : ℝ ↦ c * x) := by
  fun_prop

-- Exercise 7: The function x ↦ x^2 is continuous on ℝ
example : Continuous (fun x : ℝ ↦ x ^ 2) := by
  fun_prop

-- Exercise 8: The first projection is continuous
example : Continuous (Prod.fst : ℝ × ℝ → ℝ) := by
  exact continuous_fst

/- ## Part 2: Open and Closed Sets -/

-- Exercise 9: The empty set is open
example : IsOpen (∅ : Set ℝ) := by
  exact isOpen_empty

-- Exercise 10: The whole space is open
example : IsOpen (Set.univ : Set ℝ) := by
  exact isOpen_univ

-- Exercise 11: The preimage of an open set under a continuous function is open
example (f : ℝ → ℝ) (hf : Continuous f) (s : Set ℝ) (hs : IsOpen s) :
    IsOpen (f ⁻¹' s) := by
  exact hs.preimage hf

-- Exercise 12: The empty set is closed
example : IsClosed (∅ : Set ℝ) := by
  exact isClosed_empty

-- Exercise 13: A singleton is closed in ℝ
example (x : ℝ) : IsClosed ({x} : Set ℝ) := by
  exact isClosed_singleton

-- Exercise 14: The union of two open sets is open
example (s t : Set ℝ) (hs : IsOpen s) (ht : IsOpen t) : IsOpen (s ∪ t) := by
  exact hs.union ht

-- Exercise 15: The intersection of two open sets is open
example (s t : Set ℝ) (hs : IsOpen s) (ht : IsOpen t) : IsOpen (s ∩ t) := by
  exact hs.inter ht

/- ## Part 3: Metric Spaces -/

-- Exercise 16: dist x x = 0
example (x : ℝ) : dist x x = 0 := by
  exact dist_self x

-- Exercise 17: dist is symmetric
example (x y : ℝ) : dist x y = dist y x := by
  exact dist_comm x y

-- Exercise 18: Triangle inequality
example (x y z : ℝ) : dist x z ≤ dist x y + dist y z := by
  exact dist_triangle x y z

-- Exercise 19: dist is nonneg
example (x y : ℝ) : 0 ≤ dist x y := by
  exact dist_nonneg

-- Exercise 20: In a metric space, open balls are open.
example {X : Type*} [MetricSpace X] (x : X) (r : ℝ) :
    IsOpen (Metric.ball x r) := by
  exact Metric.isOpen_ball

/- ## Part 4: Compact Sets -/

-- Exercise 21: A closed interval is compact
example (a b : ℝ) : IsCompact (Set.Icc a b) := by
  exact isCompact_Icc

-- Exercise 22: The image of a compact set under a continuous function is compact
example (f : ℝ → ℝ) (hf : Continuous f) (K : Set ℝ) (hK : IsCompact K) :
    IsCompact (f '' K) := by
  exact hK.image hf

-- Exercise 23: A continuous function on a compact set attains its maximum.
-- Hint: IsCompact.exists_isMaxOn, or bounded/closed arguments.
example (f : ℝ → ℝ) (hf : Continuous f) (a b : ℝ) (hab : a ≤ b) :
    ∃ x ∈ Set.Icc a b, ∀ y ∈ Set.Icc a b, f y ≤ f x := by
  obtain ⟨x, hx, hmax⟩ := isCompact_Icc.exists_isMaxOn (Set.nonempty_Icc.mpr hab) hf.continuousOn
  exact ⟨x, hx, fun y hy ↦ hmax hy⟩

/- ## Part 5: Filters and Topology -/

-- Exercise 24: f is continuous iff it is continuous at every point.
example {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (f : X → Y) :
    Continuous f ↔ ∀ x, ContinuousAt f x := by
  exact continuous_iff_continuousAt

-- Exercise 25: f is continuous at x iff Tendsto f (nhds x) (nhds (f x)).
example {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (f : X → Y)
    (x : X) : ContinuousAt f x ↔ Tendsto f (nhds x) (nhds (f x)) := by
  exact Iff.rfl
