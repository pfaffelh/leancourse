import Mathlib.Tactic

/-!
# (witness) 2.2-a -- Sets

*Notes chapter 2.2, week 9.*
-/

variable (α β : Type)
variable (s t u v : Set α)

open Set

theorem subset_def : s ⊆ t ↔ ∀ x, x ∈ s → x ∈ t := by rfl
theorem mem_union (x : α) : x ∈ s ∪ t ↔ x ∈ s ∨ x ∈ t := by rfl
theorem mem_inter (x : α) : x ∈ s ∩ t ↔ x ∈ s ∧ x ∈ t := by rfl
theorem empty_def : ∅ = { _x : α | False } := by rfl
theorem univ_def : Set.univ = { _x : α | True } := by rfl
theorem mem_def (p : α → Prop) : x ∈ {x | p x } ↔ p x := by rfl
theorem mem_complement_def (s : Set α) : x ∈ sᶜ ↔ x ∉ s := by rfl
theorem setdiff_def (s t : Set α) : s \ t = s ∩ tᶜ := by rfl

-- Exercise 1
example : s ⊆ s := by
  intro x hx
  exact hx

-- Exercise 2
example : s ∩ t ⊆ s := by
  intro x hx
  exact hx.1

-- Exercise 3
example : s ⊆ s ∪ t := by
  intro x hx
  exact Or.inl hx

-- Exercise 4
example (hst : s ⊆ t) (htu : t ⊆ u) : s ⊆ u := by
  intro x hx
  exact htu (hst hx)

-- Exercise 5
example : s \ t ⊆ s := by
  intro x hx
  exact hx.1

-- Exercise 6
example : s \ t ⊆ tᶜ := by
  intro x hx
  exact hx.2

-- Exercise 7
example : (∀ x, x ∈ s) ↔ ¬∃ x, x ∈ sᶜ := by
  constructor
  · rintro h ⟨x, hx⟩
    exact hx (h x)
  · intro h x
    by_contra hx
    exact h ⟨x, hx⟩

example (f g : α → β) : f = g ↔ ∀ x, f x = g x := by
  constructor
  · intro h x
    rw [h]
  · intro h
    ext x
    exact h x

example : s = t ↔ ∀ x, x ∈ s ↔ x ∈ t := by
  constructor
  · intro h x
    rw [h]
  · intro h
    ext x
    exact h x

-- Exercise 8
example : s = t ↔ (s ⊆ t ∧ t ⊆ s) := by
  constructor
  · intro h
    rw [h]
    exact ⟨fun x hx => hx, fun x hx => hx⟩
  · rintro ⟨h1, h2⟩
    ext x
    exact ⟨fun hx => h1 hx, fun hx => h2 hx⟩

-- Exercise 9
example : s = sᶜᶜ := by
  ext x
  simp

-- Exercise 10
example : s = ∅ ↔ s ⊆ ∅ := by
  constructor
  · intro h
    rw [h]
  · intro h
    ext x
    exact ⟨fun hx => h hx, fun hx => hx.elim⟩
