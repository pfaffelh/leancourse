import Mathlib

/-
# (witness) 2.6-b -- Filters

*Notes chapter 2.6, week 12.*

These exercises cover the construction and use of filters in Mathlib,
including Filter.Tendsto, Filter.Eventually, and Filter.atTop.
One worked proof for each exercise.
-/

open Filter

/- ## Part 1: Principal Filters -/

-- Exercise 1: The whole space is in any filter
example {α : Type*} (F : Filter α) : Set.univ ∈ F := by
  exact Filter.univ_mem

-- Exercise 2: A set is in the principal filter 𝓟 s iff s ⊆ it
example {α : Type*} (s t : Set α) : t ∈ 𝓟 s ↔ s ⊆ t := by
  exact Filter.mem_principal

-- Exercise 3: s is in its own principal filter
example {α : Type*} (s : Set α) : s ∈ 𝓟 s := by
  exact Filter.mem_principal_self s

-- Exercise 4: If s ∈ F and s ⊆ t, then t ∈ F (upward closure)
example {α : Type*} (F : Filter α) (s t : Set α) (hs : s ∈ F) (hst : s ⊆ t) :
    t ∈ F := by
  exact F.sets_of_superset hs hst

-- Exercise 5: If s ∈ F and t ∈ F, then s ∩ t ∈ F
example {α : Type*} (F : Filter α) (s t : Set α) (hs : s ∈ F) (ht : t ∈ F) :
    s ∩ t ∈ F := by
  exact F.inter_sets hs ht

/- ## Part 2: The atTop Filter -/

-- Exercise 6: The set {n : ℕ | n ≥ 0} is in atTop
example : {n : ℕ | n ≥ 0} ∈ (atTop : Filter ℕ) := by
  simp

-- Exercise 7: The set {n : ℕ | n ≥ 1000} is in atTop
example : {n : ℕ | n ≥ 1000} ∈ (atTop : Filter ℕ) := by
  exact Filter.eventually_atTop.mpr ⟨1000, fun n hn => hn⟩

-- Exercise 8: The set of even numbers is NOT in atTop
-- (This is harder; you may skip it)
-- Hint: show that for any N, there exists n ≥ N with n odd.
example : {n : ℕ | n % 2 = 0} ∉ (atTop : Filter ℕ) := by
  intro h
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp h
  have := hN (2 * N + 1) (by omega)
  omega

/- ## Part 3: Filter.Eventually -/

-- Exercise 9: Eventually n ≥ 100 with respect to atTop
example : ∀ᶠ n in (atTop : Filter ℕ), n ≥ 100 := by
  exact Filter.eventually_atTop.mpr ⟨100, fun n hn => hn⟩

-- Exercise 10: If p holds eventually and q holds eventually, then p ∧ q holds eventually
example {α : Type*} {F : Filter α} {p q : α → Prop}
    (hp : ∀ᶠ x in F, p x) (hq : ∀ᶠ x in F, q x) :
    ∀ᶠ x in F, p x ∧ q x := by
  exact hp.and hq

-- Exercise 11: If p implies q and p holds eventually, then q holds eventually
example {α : Type*} {F : Filter α} {p q : α → Prop}
    (hpq : ∀ x, p x → q x) (hp : ∀ᶠ x in F, p x) :
    ∀ᶠ x in F, q x := by
  exact hp.mono fun x hx => hpq x hx

-- Exercise 12: Eventually, n + 1 > n
example : ∀ᶠ n in (atTop : Filter ℕ), n + 1 > n := by
  exact Filter.Eventually.of_forall fun n => Nat.lt_succ_self n

/- `filter_upwards` is the tactic for all of these. To prove
`∀ᶠ x in F, r x` from hypotheses `h₁ : ∀ᶠ x in F, p₁ x`, ...,
write

  filter_upwards [h₁, ..., hₙ] with x hp₁ ... hpₙ

and you are left with the pointwise goal `r x`, with each `hpᵢ : pᵢ x`
in context. It replaces the intersection argument that exercises 10
and 11 ask you to do by hand. -/

example : ∀ᶠ n in (atTop : Filter ℕ), 100 ≤ n ∧ n ≤ n ^ 2 := by
  filter_upwards [eventually_ge_atTop 100] with n hn
  exact ⟨hn, Nat.le_self_pow (by norm_num) n⟩

-- Exercise 13: Same tactic, two hypotheses.
example {α : Type*} {F : Filter α} {f g : α → ℝ}
    (hf : ∀ᶠ x in F, 0 ≤ f x) (hg : ∀ᶠ x in F, f x ≤ g x) :
    ∀ᶠ x in F, 0 ≤ g x := by
  filter_upwards [hf, hg] with x h1 h2
  linarith

/- ## Part 4: Filter.Tendsto -/

-- Exercise 14: The identity function tends to atTop along atTop
example : Tendsto id (atTop : Filter ℕ) atTop := by
  exact tendsto_id

-- Exercise 15: The function n ↦ n + 1 tends to atTop along atTop
example : Tendsto (fun n : ℕ ↦ n + 1) atTop atTop := by
  exact Filter.tendsto_atTop_mono (fun n => Nat.le_succ n) tendsto_id

-- Exercise 16: The function n ↦ 2 * n tends to atTop along atTop
example : Tendsto (fun n : ℕ ↦ 2 * n) atTop atTop := by
  exact Filter.tendsto_atTop_mono (fun n => Nat.le_mul_of_pos_left n (by norm_num)) tendsto_id

-- Exercise 17: A constant sequence converges to that constant
example (c : ℝ) : Tendsto (fun _ : ℕ ↦ c) atTop (nhds c) := by
  exact tendsto_const_nhds

-- Exercise 18: If f tends to l and g tends to m, then f + g tends to l + m
-- Hint: use Filter.Tendsto.add
example (f g : ℕ → ℝ) (l m : ℝ)
    (hf : Tendsto f atTop (nhds l)) (hg : Tendsto g atTop (nhds m)) :
    Tendsto (f + g) atTop (nhds (l + m)) := by
  exact hf.add hg

/- ## Part 5: Relating Filters and Sequences -/

-- Exercise 19: A sequence converging to 0 is eventually bounded by any ε > 0
-- Hint: use Metric.tendsto_atTop
example (a : ℕ → ℝ) (ha : Tendsto a atTop (nhds 0)) (ε : ℝ) (hε : ε > 0) :
    ∀ᶠ n in atTop, |a n| < ε := by
  have := Metric.tendsto_atTop.mp ha ε hε
  obtain ⟨N, hN⟩ := this
  filter_upwards [Filter.eventually_ge_atTop N] with n hn
  simpa using hN n hn

-- Exercise 20: Composition of Tendsto. A sequence shifted by one has
-- the same limit. `tendsto_add_atTop_nat 1` says that `n ↦ n + 1`
-- tends to `atTop`; compose it with `ha` using `Tendsto.comp`.
example {a : ℕ → ℝ} {l : ℝ} (ha : Tendsto a atTop (nhds l)) :
    Tendsto (fun n ↦ a (n + 1)) atTop (nhds l) := by
  exact ha.comp (tendsto_add_atTop_nat 1)

-- Exercise 21: The squeeze theorem for filters
-- If a ≤ b ≤ c eventually and a → l and c → l, then b → l
-- Hint: use tendsto_of_tendsto_of_tendsto_of_le_of_le
example (a b c : ℕ → ℝ) (l : ℝ)
    (ha : Tendsto a atTop (nhds l))
    (hc : Tendsto c atTop (nhds l))
    (hab : ∀ᶠ n in atTop, a n ≤ b n)
    (hbc : ∀ᶠ n in atTop, b n ≤ c n) :
    Tendsto b atTop (nhds l) := by
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' ha hc hab hbc

/- ## Part 6: Building filters from scratch

These exercises follow the b-mehta/Buzzard pedagogy: a filter is a
"generalized subset" defined by which actual subsets contain it.
Here you construct filters by hand, verifying the three axioms
(univ_sets, sets_of_superset, inter_sets).
-/

-- Exercise 22: Construct the principal filter 𝓟 s by hand.
-- A set t is "in 𝓟 s" iff s ⊆ t.
example {α : Type*} (s : Set α) : Filter α where
  sets := {t | s ⊆ t}
  univ_sets := by
    exact fun _ _ => trivial
  sets_of_superset := by
    exact fun hst htu => hst.trans htu
  inter_sets := by
    exact fun hs ht => Set.subset_inter hs ht

-- Exercise 23: Construct the cofinite filter by hand.
-- Hint: compl_univ, Set.finite_empty, compl_subset_compl,
-- Set.Finite.subset, compl_inter, Set.Finite.union.
example (α : Type*) : Filter α where
  sets := {s : Set α | sᶜ.Finite}
  univ_sets := by
    simp
  sets_of_superset := by
    intro s t hs hst
    exact hs.subset (Set.compl_subset_compl.mpr hst)
  inter_sets := by
    intro s t hs ht
    simp only [Set.mem_setOf_eq, Set.compl_inter] at *
    exact hs.union ht

-- Exercise 24: Construct atTop' on a nonempty linear order.
-- A set is "big" if it contains a tail [x, ∞).
example (L : Type*) [LinearOrder L] (e : L) : Filter L where
  sets := {X : Set L | ∃ x : L, ∀ y, x ≤ y → y ∈ X}
  univ_sets := by
    exact ⟨e, fun y _ => trivial⟩
  sets_of_superset := by
    rintro X Y ⟨x, hx⟩ hXY
    exact ⟨x, fun y hy => hXY (hx y hy)⟩
  inter_sets := by
    rintro X Y ⟨x, hx⟩ ⟨y, hy⟩
    refine ⟨max x y, fun z hz => ⟨hx z ?_, hy z ?_⟩⟩
    · exact (le_max_left x y).trans hz
    · exact (le_max_right x y).trans hz

-- Exercise 25: Construct the pushforward map' by hand.
-- Hint: a set s : Set β is in (map' m F) iff m ⁻¹' s ∈ F.
example {α β : Type*} (F : Filter α) (m : α → β) : Filter β where
  sets := {s | m ⁻¹' s ∈ F}
  univ_sets := by
    simp
  sets_of_superset := by
    intro s t hs hst
    exact F.sets_of_superset hs (Set.preimage_mono hst)
  inter_sets := by
    intro s t hs ht
    exact F.inter_sets hs ht

/- ## Part 7: The order on filters

Filters carry a partial order: F ≤ G means G.sets ⊆ F.sets, i.e.
"the smaller filter has more sets". This matches the generalized-subset
intuition: F ≤ G means F is contained in G as a generalized subset.
-/

-- Exercise 26: 𝓟 s ≤ 𝓟 t ↔ s ⊆ t.
example {α : Type*} (s t : Set α) : 𝓟 s ≤ 𝓟 t ↔ s ⊆ t := by
  exact Filter.principal_mono

-- Exercise 27: F ≤ 𝓟 s ↔ s ∈ F.
example {α : Type*} (F : Filter α) (s : Set α) :
    F ≤ 𝓟 s ↔ s ∈ F := by
  exact Filter.le_principal_iff

-- Exercise 28: ⊥ ≤ F for every filter F.
example {α : Type*} (F : Filter α) : ⊥ ≤ F := by
  exact bot_le

-- Exercise 29: F ≤ ⊤ for every filter F.
example {α : Type*} (F : Filter α) : F ≤ ⊤ := by
  exact le_top

-- Exercise 30: On ℕ, the cofinite filter is ≤ atTop.
-- (Every set in atTop has finite complement.)
example : (cofinite : Filter ℕ) ≤ atTop := by
  exact Nat.cofinite_eq_atTop ▸ le_rfl
