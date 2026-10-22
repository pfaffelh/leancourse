import Mathlib.Tactic

/-!
# (witness) 2.1-b -- Image and preimage

*Notes chapter 2.1, week 8.*
-/

variable (α β : Type) (f : α → β) (s : Set α) (t : Set β)

example : f '' (f ⁻¹' t) ⊆ t := by
  intro x hx
  obtain ⟨y, ⟨hy1, hy2⟩⟩ := hx
  rw [← hy2]
  exact hy1

example : s ⊆ f ⁻¹' (f '' s) := by
  intro x hx
  change f x ∈ f '' s
  use x

-- Exercise 1
example : f '' s ⊆ t ↔ s ⊆ f ⁻¹' t := by
  refine ⟨fun h x hx ↦ ?_, fun h y hy ↦ ?_⟩
  · apply h
    use x
  · obtain ⟨x, ⟨hs1, hx2⟩⟩ := hy
    rw [← hx2]
    apply h hs1

-- Exercise 2
example : id ⁻¹' s = s := by
  rfl

-- Exercise 3
example : id '' s = s := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact hy
  · intro hx
    exact ⟨x, hx, rfl⟩

variable (γ : Type) (g : β → γ) (U : Set γ)

-- Exercise 4
example : g ∘ f ⁻¹' U = f ⁻¹' (g ⁻¹' U) := by
  rfl

-- Exercise 5
example : g ∘ f '' s = g '' (f '' s) := by
  ext z
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨f x, ⟨x, hx, rfl⟩, rfl⟩
  · rintro ⟨y, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨x, hx, rfl⟩

-- Exercise 6
example (U V : Set β) : f ⁻¹' (U ∪ V) = f ⁻¹' U ∪ f ⁻¹' V := by
  rfl

-- Exercise 7
example (U V : Set β) : f ⁻¹' (U ∩ V) = f ⁻¹' U ∩ f ⁻¹' V := by
  rfl

-- Exercise 8
example (s₁ s₂ : Set α) : f '' (s₁ ∪ s₂) = f '' s₁ ∪ f '' s₂ := by
  ext y
  constructor
  · rintro ⟨x, hx | hx, rfl⟩
    · exact Or.inl ⟨x, hx, rfl⟩
    · exact Or.inr ⟨x, hx, rfl⟩
  · rintro (⟨x, hx, rfl⟩ | ⟨x, hx, rfl⟩)
    · exact ⟨x, Or.inl hx, rfl⟩
    · exact ⟨x, Or.inr hx, rfl⟩

-- Exercise 9
example (s₁ s₂ : Set α) : f '' (s₁ ∩ s₂) ⊆ f '' s₁ ∩ f '' s₂ := by
  rintro y ⟨x, ⟨h1, h2⟩, rfl⟩
  exact ⟨⟨x, h1, rfl⟩, ⟨x, h2, rfl⟩⟩

-- Exercise 10
example (s₁ s₂ : Set α) (h : s₁ ⊆ s₂) : f '' s₁ ⊆ f '' s₂ := by
  rintro y ⟨x, hx, rfl⟩
  exact ⟨x, h hx, rfl⟩

-- Exercise 11
example (U V : Set β) (h : U ⊆ V) : f ⁻¹' U ⊆ f ⁻¹' V := by
  intro x hx
  exact h hx

-- Exercise 12
example : f ⁻¹' (Set.univ : Set β) = Set.univ := by
  rfl

-- Exercise 13
example : f ⁻¹' (∅ : Set β) = ∅ := by
  rfl
