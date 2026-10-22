import Mathlib

/-!
# (witness) 1.5-c -- The Curry-Howard correspondence

*Notes chapter 1.5, week 6.*
-/

variable (P Q R S : Prop)

/- ## Part 1: Term-mode proofs for basic logic -/

example : P → P := fun h => h

example : P → Q → P := fun hP _ => hP

example : (P → Q) → (Q → R) → P → R := fun f g h => g (f h)

example (hP : P) (hQ : Q) : P ∧ Q := ⟨hP, hQ⟩

example (h : P ∧ Q) : P := h.1

example : P ∧ Q → Q ∧ P := fun h => ⟨h.2, h.1⟩

example (hP : P) : P ∨ Q := Or.inl hP

example : P ∨ Q → (P → R) → (Q → R) → R := fun h f g => h.elim f g

example : P ∨ Q → Q ∨ P := fun h => h.elim Or.inr Or.inl

example : P ∧ (Q ∨ R) → (P ∧ Q) ∨ (P ∧ R) :=
  fun h => h.2.elim (fun hq => Or.inl ⟨h.1, hq⟩) (fun hr => Or.inr ⟨h.1, hr⟩)

/- ## Part 2: Negation as function to False -/

example : (P → Q) → ¬Q → ¬P := fun f hnq hp => hnq (f hp)

example : P → ¬P → Q := fun hp hnp => (hnp hp).elim

example : ¬(P ∨ Q) → ¬P ∧ ¬Q :=
  fun h => ⟨fun hp => h (Or.inl hp), fun hq => h (Or.inr hq)⟩

/- ## Part 3: Side-by-side comparison -/

example : (P → Q) → (P → R) → P → Q ∧ R := by
  intro f g hp
  exact ⟨f hp, g hp⟩

example : (P → Q) → (P → R) → P → Q ∧ R :=
  fun f g hp => ⟨f hp, g hp⟩

example : P ∧ (Q ∧ R) → (P ∧ Q) ∧ R := by
  intro h
  exact ⟨⟨h.1, h.2.1⟩, h.2.2⟩

example : P ∧ (Q ∧ R) → (P ∧ Q) ∧ R :=
  fun h => ⟨⟨h.1, h.2.1⟩, h.2.2⟩

/- ## Part 4: Quantifiers as dependent types -/

example : ∀ (n : ℕ), n + 0 = n := fun _ => rfl

example : ∃ (n : ℕ), n * n = 16 := ⟨4, rfl⟩

example (h : ∀ (n : ℕ), n < n + 1) : ∃ (n : ℕ), n < n + 1 := ⟨0, h 0⟩

example : (∀ (n : ℕ), P → n = n) := fun _ _ => rfl

example : ∃ (n : ℕ), n > 10 ∧ n < 15 := ⟨11, by norm_num, by norm_num⟩

/- ## Part 5: Challenge problems -/

example : (P ↔ Q) → (Q ↔ R) → (P ↔ R) :=
  fun h1 h2 => ⟨fun hp => h2.1 (h1.1 hp), fun hr => h1.2 (h2.2 hr)⟩

example : ∀ (n : ℕ), ∃ (k : ℕ), n + n = 2 * k :=
  fun n => ⟨n, by omega⟩

set_option linter.defProp false in
def modusPonens : (P → Q) → P → Q :=
  fun f hp => f hp

set_option linter.defProp false in
def flip' (f : P → Q → R) : Q → P → R :=
  fun hq hp => f hp hq
