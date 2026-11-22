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

/-! ## Part 4: Functions and predicates

A function is a term `fun x => e`, so `use` can supply one as the
witness of an `∃`. `let` gives it a name first. -/

example (a : α) : ∃ (f : α → α), ∀ x, f x = a := by
  use fun _ => a
  intro x
  rfl

example (a : α) : ∃ (f : α → α), ∀ x, f x = a := by
  let f : α → α := fun _ => a
  use f
  intro x
  rfl

/-! A predicate is a function into `Prop`, built the same way. -/

example (f g : α → Prop) :
    ∃ (h : α → Prop), ∀ x, h x = (f x ∧ g x) := by
  use fun x => f x ∧ g x
  intro x
  rfl

-- Exercise 8) Give `f` and `g` explicitly. Constant functions do.
example : ∃ (f g : α → Prop), ∀ x, f x ↔ ¬(g x) := by
  use fun _ => True, fun _ => False
  intro x
  simp

-- Exercise 9) The same with `Bool`. Put the cursor on `xor` and
-- press `F12` to see its definition.
example : ∃ (f g : α → Bool), ∀ x, xor (f x) (g x) := by
  use fun _ => true, fun _ => false
  intro x
  simp

/-! ## Part 5: Equal functions -/

example : (fun n : ℕ => 0 + n) = (fun n => n) := by
  ext n
  simp

-- Exercise 10)
example (f g : α → β) : (∀ x, f x = g x) ↔ f = g := by
  constructor
  · intro h
    ext x
    exact h x
  · intro h x
    rw [h]

-- Exercise 11)
example (a : α) :
    (∀ (f g : α → β), f = g) → (∀ (y₁ y₂ : β), y₁ = y₂) := by
  intro h y₁ y₂
  have hfg := h (fun _ => y₁) (fun _ => y₂)
  change (fun _ => y₁) a = (fun _ => y₂) a
  rw [hfg]

/-! ## Part 6: Equal propositions -/

example (P Q : Prop) (h : P ↔ Q) : P = Q := propext h

-- Exercise 12)
example (P : Prop) (hP : P) : P = True := by
  apply propext
  constructor
  · intro _
    trivial
  · intro _
    exact hP

-- Exercise 13)
example (P Q : α → Prop) :
    (fun x => P x ∧ Q x) = (fun x => Q x ∧ P x) := by
  ext x
  constructor
  · intro h
    exact ⟨h.2, h.1⟩
  · intro h
    exact ⟨h.2, h.1⟩

/-! With `propext`, `rw [h]` also works for `h : P ↔ Q`: it replaces
`P` by `Q`, because the two are now equal. The following `l1` says
that an implication is a disjunction; it is in Mathlib as
`imp_iff_or_not`. -/

lemma l1 (P Q : Prop) : (P → Q) ↔ (Q ∨ ¬P) := by
  constructor
  · intro hPQ
    by_cases h : P
    · left
      exact hPQ h
    · right
      exact h
  · intro h hP
    obtain (h1 | h2) := h
    · exact h1
    · exact absurd hP h2

-- Exercise 14) Peirce's law. `rw [l1]` rewrites the innermost
-- implication; three times turn the goal into a statement about `∨`
-- and `¬`. Then `by_cases` on `P`. `rintro (h1 | h2)` splits a
-- disjunction while introducing it.
example (P Q : Prop) : ((P → Q) → P) → P := by
  rw [l1, l1, l1]
  by_cases hP : P
  · left
    exact hP
  · right
    rintro (h1 | h2)
    · exact hP h1
    · exact h2 (Or.inr hP)

-- Exercise 15) `exact?` finds this one (`not_imp_not`). Do it with
-- `rw` instead: rewrite both sides with `l1`, then `tauto`. `l1`
-- takes the two propositions as arguments, so you can say which
-- instance you mean.
lemma l2 (P Q : Prop) : (P → Q) ↔ (¬Q → ¬P) := by
  rw [l1 P Q, l1 (¬Q) (¬P)]
  tauto

/-! ## Part 7: Choice -/

noncomputable def pick (h : ∃ n : ℕ, 5 < n) : ℕ :=
  Classical.choose h

example (h : ∃ n : ℕ, 5 < n) : 5 < pick h :=
  Classical.choose_spec h

-- Exercise 16)
def pick' (h : ∃ n : ℕ, 5 < n) : ℕ :=
  Nat.find h

#eval pick' ⟨10, by decide⟩   -- 6

-- Exercise 17)
example (h : ∃ n : ℕ, 5 < n) : 5 < pick' h :=
  Nat.find_spec h

example (h : ∀ n : ℕ, ∃ m, n < m) : ∃ f : ℕ → ℕ, ∀ n, n < f n := by
  choose f hf using h
  exact ⟨f, hf⟩

-- Exercise 18)
example (R : α → α → Prop) (h : ∀ x, ∃ y, R x y)
    (hR : ∀ x y, R x y → R y x) : ∃ f : α → α, ∀ x, R (f x) x := by
  choose f hf using h
  exact ⟨f, fun x => hR x (f x) (hf x)⟩

-- Exercise 19)
example (h : Nonempty α) : ∃ x : α, x = x := by
  obtain ⟨x⟩ := h
  exact ⟨x, rfl⟩

-- Exercise 20)
noncomputable def someElement (h : Nonempty α) : α :=
  Classical.choice h
