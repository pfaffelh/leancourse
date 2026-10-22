import Mathlib

/-!
# (witness) X-a -- Puzzles

*Extra sheet, week 5. Nothing depends on it.*

Solvability witness for `Exercises/99-Extra/a-Puzzles.lean`.
Not teaching material; see `Leancourse/Checks/README.md`.
-/

/-! ## The drinker paradox -/

example (α : Type) [Inhabited α] (P : α → Prop) : ∃ x, P x → ∀ y, P y := by
  by_cases h : ∀ y, P y
  · exact ⟨default, fun _ => h⟩
  · push Not at h
    obtain ⟨y, hy⟩ := h
    exact ⟨y, fun hPy => absurd hPy hy⟩

/-! ## The hardest level -/

example (α : Type) [Inhabited α] (R : α → Prop) (f : α → α)
    (h : ∀ x, ¬R x → R (f x)) : ∃ x, R x ∧ R (f (f x)) := by
  obtain ⟨b, hb⟩ : ∃ b, R b := by
    by_cases hd : R (default : α)
    · exact ⟨default, hd⟩
    · exact ⟨f default, h default hd⟩
  by_cases h2 : R (f (f b))
  · exact ⟨b, hb, h2⟩
  · refine ⟨f b, ?_, h (f (f b)) h2⟩
    by_cases h1 : R (f b)
    · exact h1
    · exact absurd (h (f b) h1) h2

/-! ## Knights and knaves -/

example (A B : Prop) (h : A ↔ ¬A ∧ ¬B) : ¬A ∧ B := by
  have na : ¬A := fun a => (h.mp a).1 a
  refine ⟨na, ?_⟩
  by_contra nb
  exact na (h.mpr ⟨na, nb⟩)
