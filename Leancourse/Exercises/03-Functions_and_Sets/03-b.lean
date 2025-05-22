-- Again, we only import tactics
import Mathlib.Tactic -- imports all the Lean tactics

variable (α β : Type)

/- # Sets in Lean

Informally, types and sets are similar things, both are collections of some kind. However, since Lean is strict, we have to be careful with the details. Let us see what a Set is in Lean:

-/

#print Set

/- Most importantly, `s : Set α` is equivalent to some function `s : α → Prop`. The idea is that `x ∈ s` iff `s x` is True. In this sense, you can apply the set `s` to some `x : α` and will hear back `True` if `x ∈ s` and `False` otherwise. -/

variable (s t u v : Set α) -- s t u v are sets within type `α`:

open Set

/- # Subset, intersection, union, etc


Here are some mathematical facts, which are true by definition:

-/
theorem subset_def : s ⊆ t ↔ ∀ x, x ∈ s → x ∈ t := by
  rfl

theorem mem_union (x : α) : x ∈ s ∪ t ↔ x ∈ s ∨ x ∈ t := by
  rfl

theorem mem_inter (x : α) : x ∈ s ∩ t ↔ x ∈ s ∧ x ∈ t := by
  rfl

theorem empty_def : ∅ = { _x : α | False }  := by
  rfl

theorem univ_def : Set.univ = { _x : α | True }  := by
  rfl

theorem mem_def (p : α → Prop) : x ∈ {x | p x } ↔ p x := by
  rfl

theorem mem_complement_def (s : Set α) : x ∈ sᶜ ↔ x ∉ s := by
  rfl

theorem setdiff_def (s t : Set α) : s \ t = s ∩ tᶜ := by
  rfl

-- Exercise 1
example : s ⊆ s := by
  sorry

-- Exercise 2
example : s ∩ t ⊆ s := by
  sorry

-- Exercise 3
example : s ⊆ s ∪ t := by
  sorry

-- Exercise 4
example (hst : s ⊆ t) (htu : t ⊆ u) : s ⊆ u := by
  sorry

-- Exercise 5
example : s \ t ⊆ s := by
  sorry

-- Exercise 6
example : s \ t ⊆ tᶜ := by
  sorry

-- Exercise 7
example : (∀ x, x ∈ s) ↔ ¬∃ x, x ∈ sᶜ := by
  sorry

/-
# Extensionality

When are two sets equal? Well, if they contain the same elements. This is what extensionality is about.

If the goal is `⊢ s = t` where `a` and `b` are `Set α`, then `ext x,` will create a hypothesis `x : α` and change
the goal to `x ∈ A ↔ x ∈ B`.

Since we will be dealing with sets below anyway, we start with a different example. Two functions are equal, if all values are equal.

-/

example (f g : α → β) : f = g ↔ ∀ x, f x = g x := by
  constructor
  · intro h x
    rw [h]
  · intro h
    ext x
    exact h x

/- For sets this is similar, and the proof is the same, letter by letter: -/

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
  · sorry
  · sorry

-- Exercise 9
example : s = sᶜᶜ := by
  sorry

-- Exercise 10
example : s = ∅ ↔ s ⊆ ∅ := by
  sorry
