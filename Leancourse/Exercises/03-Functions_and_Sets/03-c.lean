import Mathlib.Tactic -- imports all the Lean tactics

/- Let us now combine the last two topics, functions and sets: You know both, the image (or push-forward) of a set under a function/map, and the pre-image (or pull-back) of a set under some function/map.

In Lean, consider `f : α → β` and `s : Set α`, and write `f '' s := { y : β | ∃ x : α, x ∈ s ∧ f x = y}`, and call it the push-forward of `s` along `f`.

In addition, for `f : α → β` and `t : Set β`, write `f⁻¹' t := { x : α | f x ∈ t}`, and call it the pull-back of `t` along `f`.

**Important note**: If we write `y ∈ f '' s`, we actually have a triple `⟨x, ⟨h₀, h₁⟩⟩`, where `x` is such that `x ∈ s` and `f x = y`.
However, if we write `x ∈ f⁻¹' t`, this is equivalent to `f x ∈ t`.
Both cases will be important below.

-/

variable (α β : Type) (f : α → β) (s : Set α) (t : Set β)

example : f '' (f ⁻¹' t) ⊆ t := by
  intro x hx
  obtain ⟨y, ⟨hy1, hy2⟩⟩ := hx -- this is the triple from above
  rw [← hy2]
  exact hy1

example : s ⊆ f ⁻¹' (f '' s) := by
  intro x hx
  change f x ∈ f '' s -- this is the same by definition, see above
  use x

-- Exercise 1:
-- `exact?` will do this but see if you can do it yourself.
example : f '' s ⊆ t ↔ s ⊆ f ⁻¹' t := by
  sorry

-- Exercise 2:
-- Pushforward and pullback along the identity map don't change anything
-- pullback is actually simple:
example : id ⁻¹' s = s := by
  sorry

-- Exercise 3:
-- pushforward is a little trickier. Probablty, you will use `ext x` and `constructor`.
example : id '' s = s := by
  sorry

-- Now let's try composition.
variable (γ : Type) (g : β → γ) (U : Set γ)

-- Exercise 4:
-- As you know, the preimage of a preimage is the preimage of a composition.
example : g ∘ f ⁻¹' U = f ⁻¹' (g ⁻¹' U) := by
  sorry

-- Exercise 5:
-- The same holds for images.
example : g ∘ f '' s = g '' (f '' s) := by
  sorry
