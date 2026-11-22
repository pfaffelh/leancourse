import Mathlib

/-!
# (witness) 1.5-a -- Rules, equality and choice

*Notes chapter 1.5, week 6.*
-/

variable (α β : Type)

/-! ## Part 1: Universes -/

-- Exercise 1)
#check ℕ → ℕ                  -- Type
#check ℕ → Type               -- Type 1
#check Type → Type            -- Type 1
#check ∀ n : ℕ, n + 0 = n     -- Prop
#check ∀ p : Prop, p → p      -- Prop
#check (γ : Type) → γ → γ     -- Type 1

-- Exercise 2)
example : Type 1 := Type
example : ℕ → Type := fun n => Fin n
example : (γ : Type) → γ → γ := fun _ x => x

/-! ## Part 2: Conversion -/

def dbl (n : ℕ) : ℕ := n + n

example : dbl 3 = 6 := by
  rfl

-- Exercise 3)
example : (fun n : ℕ => n * n + 1) 3 = 10 := by
  rfl

-- Exercise 4)
example (P : Prop) : ¬P ↔ (P → False) := by
  rfl

example (P : Prop) (h : ¬¬P) (hn : ¬P) : False := by
  change (P → False) → False at h
  exact h hn

-- Exercise 5)
example (P : Prop) (hP : P) : ¬¬P := by
  change (P → False) → False
  intro h
  exact h hP

/-! ## Part 3: Proofs carry no data -/

example (P : Prop) (h₁ h₂ : P) : h₁ = h₂ := by
  rfl

-- Exercise 6)
example (h₁ h₂ : 2 < 5) : (⟨2, h₁⟩ : Fin 5) = ⟨2, h₂⟩ := by
  rfl

-- Exercise 7)
example (h : ∃ n : ℕ, 3 < n) : ∃ n : ℕ, 2 < n := by
  obtain ⟨n, hn⟩ := h
  exact ⟨n, by omega⟩

/-! ## Part 4: Equal functions -/

example : (fun n : ℕ => 0 + n) = (fun n => n) := by
  ext n
  simp

-- Exercise 8)
example (f g : α → β) : (∀ x, f x = g x) ↔ f = g := by
  constructor
  · intro h
    ext x
    exact h x
  · intro h x
    rw [h]

-- Exercise 9)
example (a : α) :
    (∀ (f g : α → β), f = g) → (∀ (y₁ y₂ : β), y₁ = y₂) := by
  intro h y₁ y₂
  have hfg := h (fun _ => y₁) (fun _ => y₂)
  change (fun _ => y₁) a = (fun _ => y₂) a
  rw [hfg]

/-! ## Part 5: Equal propositions -/

example (P Q : Prop) (h : P ↔ Q) : P = Q := propext h

-- Exercise 10)
example (P : Prop) (hP : P) : P = True := by
  apply propext
  constructor
  · intro _
    trivial
  · intro _
    exact hP

-- Exercise 11)
example (P Q : α → Prop) :
    (fun x => P x ∧ Q x) = (fun x => Q x ∧ P x) := by
  ext x
  constructor
  · intro h
    exact ⟨h.2, h.1⟩
  · intro h
    exact ⟨h.2, h.1⟩

/-! ## Part 6: Choice -/

noncomputable def pick (h : ∃ n : ℕ, 5 < n) : ℕ :=
  Classical.choose h

example (h : ∃ n : ℕ, 5 < n) : 5 < pick h :=
  Classical.choose_spec h

-- Exercise 12)
def pick' (h : ∃ n : ℕ, 5 < n) : ℕ :=
  Nat.find h

#eval pick' ⟨10, by decide⟩   -- 6

-- Exercise 13)
example (h : ∃ n : ℕ, 5 < n) : 5 < pick' h :=
  Nat.find_spec h

example (h : ∀ n : ℕ, ∃ m, n < m) : ∃ f : ℕ → ℕ, ∀ n, n < f n := by
  choose f hf using h
  exact ⟨f, hf⟩

-- Exercise 14)
example (R : α → α → Prop) (h : ∀ x, ∃ y, R x y)
    (hR : ∀ x y, R x y → R y x) : ∃ f : α → α, ∀ x, R (f x) x := by
  choose f hf using h
  exact ⟨f, fun x => hR x (f x) (hf x)⟩

-- Exercise 15)
example (h : Nonempty α) : ∃ x : α, x = x := by
  obtain ⟨x⟩ := h
  exact ⟨x, rfl⟩

-- Exercise 16)
noncomputable def someElement (h : Nonempty α) : α :=
  Classical.choice h
