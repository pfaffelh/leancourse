import Mathlib

/-
# (witness) 2.7-a -- Topology

*Notes chapter 2.7, week 13.*

These exercises cover continuity, open and closed sets, closure and
interior, metric spaces, compactness and connectedness. Replace each `sorry` with a proof.
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

/- ## Part 3: Closure, interior, frontier

See the section *Closure, interior, and frontier* of chapter 2.7. -/

-- Exercise 16: A set is contained in its closure.
example {X : Type*} [TopologicalSpace X] (s : Set X) :
    s ⊆ closure s := by
  exact subset_closure

-- Exercise 17: The interior is contained in the set.
example {X : Type*} [TopologicalSpace X] (s : Set X) :
    interior s ⊆ s := by
  exact interior_subset

-- Exercise 18: Closure is monotone.
example {X : Type*} [TopologicalSpace X] (s t : Set X)
    (h : s ⊆ t) : closure s ⊆ closure t := by
  exact closure_mono h

-- Exercise 19: An open set is its own interior.
example {X : Type*} [TopologicalSpace X] (s : Set X)
    (hs : IsOpen s) : interior s = s := by
  exact hs.interior_eq

-- Exercise 20: The complement of the closure is the interior of the
-- complement. Search with `exact?`.
example {X : Type*} [TopologicalSpace X] (s : Set X) :
    (closure s)ᶜ = interior sᶜ := by
  exact (interior_compl).symm

-- Exercise 21: The closure of an open interval.
example : closure (Set.Ioo (0 : ℝ) 1) = Set.Icc 0 1 := by
  exact closure_Ioo zero_ne_one

-- Exercise 22: The interior of a closed interval.
example : interior (Set.Icc (0 : ℝ) 1) = Set.Ioo 0 1 := by
  exact interior_Icc

-- Exercise 23: The frontier of `[0, 1]` consists of the two endpoints.
example : frontier (Set.Icc (0 : ℝ) 1) = {0, 1} := by
  rw [frontier_Icc zero_le_one]

-- Exercise 24: In ℝ, `x` is in the closure of `s` iff `s` comes
-- arbitrarily close to `x`. Hint: `Metric.mem_closure_iff`.
example (s : Set ℝ) (x : ℝ) :
    x ∈ closure s ↔ ∀ ε > 0, ∃ y ∈ s, dist x y < ε := by
  exact Metric.mem_closure_iff

/- ## Part 4: Metric Spaces -/

-- Exercise 25: dist x x = 0
example (x : ℝ) : dist x x = 0 := by
  exact dist_self x

-- Exercise 26: dist is symmetric
example (x y : ℝ) : dist x y = dist y x := by
  exact dist_comm x y

-- Exercise 27: Triangle inequality
example (x y z : ℝ) : dist x z ≤ dist x y + dist y z := by
  exact dist_triangle x y z

-- Exercise 28: dist is nonneg
example (x y : ℝ) : 0 ≤ dist x y := by
  exact dist_nonneg

-- Exercise 29: In a metric space, open balls are open.
example {X : Type*} [MetricSpace X] (x : X) (r : ℝ) :
    IsOpen (Metric.ball x r) := by
  exact Metric.isOpen_ball

/- ## Part 5: Compact Sets -/

-- Exercise 30: A closed interval is compact
example (a b : ℝ) : IsCompact (Set.Icc a b) := by
  exact isCompact_Icc

-- Exercise 31: The image of a compact set under a continuous function is compact
example (f : ℝ → ℝ) (hf : Continuous f) (K : Set ℝ) (hK : IsCompact K) :
    IsCompact (f '' K) := by
  exact hK.image hf

-- Exercise 32: A continuous function on a compact set attains its maximum.
-- Hint: IsCompact.exists_isMaxOn, or bounded/closed arguments.
example (f : ℝ → ℝ) (hf : Continuous f) (a b : ℝ) (hab : a ≤ b) :
    ∃ x ∈ Set.Icc a b, ∀ y ∈ Set.Icc a b, f y ≤ f x := by
  obtain ⟨x, hx, hmax⟩ := isCompact_Icc.exists_isMaxOn (Set.nonempty_Icc.mpr hab) hf.continuousOn
  exact ⟨x, hx, fun y hy ↦ hmax hy⟩

/- ## Part 6: Connected Sets -/

-- Exercise 33: A closed interval is connected.
example (a b : ℝ) (hab : a ≤ b) : IsConnected (Set.Icc a b) := by
  exact isConnected_Icc hab

-- Exercise 34: The continuous image of a connected set is connected.
-- Hint: `IsConnected.image` wants `ContinuousOn`.
example (f : ℝ → ℝ) (hf : Continuous f) (s : Set ℝ)
    (hs : IsConnected s) : IsConnected (f '' s) := by
  exact hs.image f hf.continuousOn

/- ## Part 7: Filters and Topology -/

-- Exercise 35: f is continuous iff it is continuous at every point.
example {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (f : X → Y) :
    Continuous f ↔ ∀ x, ContinuousAt f x := by
  exact continuous_iff_continuousAt

-- Exercise 36: f is continuous at x iff Tendsto f (nhds x) (nhds (f x)).
example {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (f : X → Y)
    (x : X) : ContinuousAt f x ↔ Tendsto f (nhds x) (nhds (f x)) := by
  exact Iff.rfl

-- Exercise 37: If `a → l` and `f` is continuous at `l`, then
-- `f ∘ a → f l`.
example {f : ℝ → ℝ} {a : ℕ → ℝ} {l : ℝ}
    (ha : Tendsto a atTop (nhds l)) (hf : ContinuousAt f l) :
    Tendsto (f ∘ a) atTop (nhds (f l)) := by
  exact hf.tendsto.comp ha

-- Exercise 38: Construct the neighborhood filter by hand (compare
-- sheet 2.6-b, part 6). A set is a neighborhood of `x` if it
-- contains an open set containing `x`.
example {X : Type*} [TopologicalSpace X] (x : X) : Filter X where
  sets := {s : Set X | ∃ U : Set X, x ∈ U ∧ IsOpen U ∧ U ⊆ s}
  univ_sets := by
    exact ⟨Set.univ, Set.mem_univ x, isOpen_univ, Set.subset_univ _⟩
  sets_of_superset := by
    rintro s t ⟨U, hxU, hU, hUs⟩ hst
    exact ⟨U, hxU, hU, hUs.trans hst⟩
  inter_sets := by
    rintro s t ⟨U, hxU, hU, hUs⟩ ⟨V, hxV, hV, hVt⟩
    exact ⟨U ∩ V, ⟨hxU, hxV⟩, hU.inter hV,
      Set.inter_subset_inter hUs hVt⟩
