import Mathlib.Tactic -- imports all the Lean tactics

/-!
# 2.2-b -- Image and preimage

*Notes chapter 2.2, week 9.*
-/

/- Read the section *Image and preimage* of chapter 2.2 first.

For `f : α → β`, `s : Set α` and `t : Set β`:

* `f '' s = {y | ∃ x, x ∈ s ∧ f x = y}`, the image of `s`;
* `f ⁻¹' t = {x | f x ∈ t}`, the preimage of `t`.

A hypothesis `hy : y ∈ f '' s` is a triple: `obtain ⟨x, hx, rfl⟩ := hy`
gives `x`, `hx : x ∈ s`, and replaces `y` by `f x`. A hypothesis
`hx : x ∈ f ⁻¹' t` *is* `f x ∈ t`; `change f x ∈ t at hx` makes this
visible, but is not needed. -/

variable (α β : Type) (f : α → β) (s : Set α) (t : Set β)

example : f '' (f ⁻¹' t) ⊆ t := by
  rintro y ⟨x, hx, rfl⟩
  -- `hx : x ∈ f ⁻¹' t`, which is `f x ∈ t`, and the goal is `f x ∈ t`
  exact hx

example : s ⊆ f ⁻¹' (f '' s) := by
  intro x hx
  -- the goal is `f x ∈ f '' s`; name the point
  exact ⟨x, hx, rfl⟩

-- Exercise 1:
-- `Set.range f` is the image of all of `α`, and
-- `y ∈ Set.range f` means `∃ x, f x = y`. Start with `ext y` and
-- `constructor`.
example : f '' (f ⁻¹' t) = t ∩ Set.range f := by
  sorry

-- Exercise 2:
-- Pushforward and pullback along the identity map don't change
-- anything. Pullback is the simple one -- unfold both sides and
-- compare.
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

-- Exercise 6:
-- The preimage of a union is the union of preimages.
example (U V : Set β) : f ⁻¹' (U ∪ V) = f ⁻¹' U ∪ f ⁻¹' V := by
  sorry

-- Exercise 7:
-- The preimage of an intersection is the intersection of preimages.
-- Try `rfl`. Why does it work here, and not in exercise 8?
example (U V : Set β) : f ⁻¹' (U ∩ V) = f ⁻¹' U ∩ f ⁻¹' V := by
  sorry

-- Exercise 8:
-- The image of a union is the union of images.
example (s₁ s₂ : Set α) : f '' (s₁ ∪ s₂) = f '' s₁ ∪ f '' s₂ := by
  sorry

-- Exercise 9:
-- The image of an intersection is contained in the intersection of
-- images; equality needs injectivity (sheet 2.2-c). The notes cite
-- `Set.image_inter_subset`; prove it by hand.
example (s₁ s₂ : Set α) : f '' (s₁ ∩ s₂) ⊆ f '' s₁ ∩ f '' s₂ := by
  sorry

-- Exercise 10:
-- Pushforward is monotone.
example (s₁ s₂ : Set α) (h : s₁ ⊆ s₂) : f '' s₁ ⊆ f '' s₂ := by
  sorry

-- Exercise 11:
-- Pullback is monotone.
example (U V : Set β) (h : U ⊆ V) : f ⁻¹' U ⊆ f ⁻¹' V := by
  sorry

-- Exercise 12:
-- The pullback of the whole codomain is everything.
example : f ⁻¹' (Set.univ : Set β) = Set.univ := by
  sorry

-- Exercise 13:
-- The pullback of the empty set is empty.
example : f ⁻¹' (∅ : Set β) = ∅ := by
  sorry
