import Mathlib

/-!
# (witness) 2.9-a -- Monads in mathematics

*Notes chapter 2.9, week 15.*
-/

open Filter

/-! ## Part 1: Sets -/

-- Exercise 1)
example (f : ℕ → ℕ) (s : Set ℕ) : f <$> s = f '' s := rfl

-- Exercise 2)
example : (· * 2) '' ({1, 2, 3} : Set ℕ) = {2, 4, 6} := by
  simp [Set.image_insert_eq]

-- Exercise 3)
example {α : Type} (s : Set α) : id '' s = s :=
  Set.image_id s

-- Exercise 4)
example {α β γ : Type} (f : α → β) (g : β → γ) (s : Set α) :
    (g ∘ f) '' s = g '' (f '' s) :=
  Set.image_comp g f s

section SetMonad
attribute [local instance] Set.monad

-- Exercise 5)
example {α β : Type} (s : Set α) (f : α → Set β) :
    (s >>= f) = ⋃ a ∈ s, f a := rfl

-- Exercise 6)
example {α β : Type} (s : Set α) (f : α → Set β) (b : β) :
    b ∈ (s >>= f) ↔ ∃ a ∈ s, b ∈ f a := by
  simp [Set.bind_def]

end SetMonad

/-! ## Part 2: Finite sets -/

-- Exercise 7)
example : ({1, 2, 3} : Finset ℕ).image (· * 2) = {2, 4, 6} := by
  decide

-- Exercise 8)
example {α β : Type} [DecidableEq β] (f : α → β) (s : Finset α) :
    (s.image f).card ≤ s.card :=
  Finset.card_image_le

-- Exercise 9)
example {α β : Type} (f : α → β) (s : Finset α) :
    ∃ t : Finset β, t.card ≤ s.card ∧ ∀ a ∈ s, f a ∈ t := by
  classical
  exact ⟨s.image f, Finset.card_image_le,
    fun a ha => Finset.mem_image_of_mem f ha⟩

-- Exercise 10)
example : ({1, 2} : Finset ℕ).biUnion (fun n => {n, 10 * n})
    = {1, 2, 10, 20} := by
  decide

/-! ## Part 3: Filters -/

-- Exercise 11)
example {α β : Type} (m : α → β) (F : Filter α) :
    m <$> F = Filter.map m F := rfl

-- Exercise 12)
example {α β : Type} (m : α → β) (F : Filter α) (t : Set β) :
    t ∈ Filter.map m F ↔ m ⁻¹' t ∈ F := Iff.rfl

-- Exercise 13)
example {α : Type} (F : Filter α) : Filter.map id F = F :=
  Filter.map_id

-- Exercise 14)
example {α β γ : Type} (f : α → β) (g : β → γ) (F : Filter α) :
    Filter.map g (Filter.map f F) = Filter.map (g ∘ f) F :=
  Filter.map_map

-- Exercise 15)
example {α : Type} (a : α) (s : Set α) :
    s ∈ (pure a : Filter α) ↔ a ∈ s :=
  Filter.mem_pure

-- Exercise 16)
example {α β : Type} (f : α → β) (a : α) :
    Filter.map f (pure a) = pure (f a) :=
  Filter.map_pure f a

-- Exercise 17)
example {α β : Type} (f : α → β) (F : Filter α) (G : Filter β) :
    Tendsto f F G ↔ Filter.map f F ≤ G := Iff.rfl
