import Mathlib

/-
# Exercises: Orders and Lattices

These exercises cover partial orders, lattices, and complete lattices.
You will work with ≤, ⊔, ⊓, sSup, and monotone functions.
Replace each `sorry` with a proof.
-/

variable {α : Type*}

/- ## Part 1: Partial Orders -/

-- Exercise 1: Transitivity of ≤ on ℕ
example (a b c : ℕ) (hab : a ≤ b) (hbc : b ≤ c) : a ≤ c := by
  sorry

-- Exercise 2: Antisymmetry of ≤ on ℕ
example (a b : ℕ) (hab : a ≤ b) (hba : b ≤ a) : a = b := by
  sorry

-- Exercise 3: If a < b and b < c, then a < c
example (a b c : ℕ) (hab : a < b) (hbc : b < c) : a < c := by
  sorry

-- Exercise 4: If a < b then a ≤ b
example (a b : ℕ) (h : a < b) : a ≤ b := by
  sorry

-- Exercise 5: If a ≤ b and a ≠ b, then a < b
example (a b : ℕ) (h : a ≤ b) (hne : a ≠ b) : a < b := by
  sorry

/- ## Part 2: Sets and Subset Order -/

-- Exercise 6: Subset is reflexive
example (A : Set ℕ) : A ⊆ A := by
  sorry

-- Exercise 7: Subset is transitive
example (A B C : Set ℕ) (hAB : A ⊆ B) (hBC : B ⊆ C) : A ⊆ C := by
  sorry

-- Exercise 8: If A ⊆ B and B ⊆ A, then A = B
example (A B : Set ℕ) (hAB : A ⊆ B) (hBA : B ⊆ A) : A = B := by
  sorry

/- ## Part 3: Lattice Operations on Sets -/

-- Exercise 9: A ⊆ A ∪ B
example (A B : Set ℕ) : A ⊆ A ∪ B := by
  sorry

-- Exercise 10: A ∩ B ⊆ A
example (A B : Set ℕ) : A ∩ B ⊆ A := by
  sorry

-- Exercise 11: If A ⊆ C and B ⊆ C, then A ∪ B ⊆ C
example (A B C : Set ℕ) (hA : A ⊆ C) (hB : B ⊆ C) : A ∪ B ⊆ C := by
  sorry

-- Exercise 12: If C ⊆ A and C ⊆ B, then C ⊆ A ∩ B
example (A B C : Set ℕ) (hA : C ⊆ A) (hB : C ⊆ B) : C ⊆ A ∩ B := by
  sorry

-- Exercise 13: Distributivity of ∩ over ∪
example (A B C : Set ℕ) : A ∩ (B ∪ C) = (A ∩ B) ∪ (A ∩ C) := by
  sorry

/- ## Part 4: General Lattices -/

-- Exercise 14: In a lattice, a ⊔ b = b ⊔ a
example [Lattice α] (a b : α) : a ⊔ b = b ⊔ a := by
  sorry

-- Exercise 15: In a lattice, a ⊓ b = b ⊓ a
example [Lattice α] (a b : α) : a ⊓ b = b ⊓ a := by
  sorry

-- Exercise 16: a ≤ a ⊔ b
example [Lattice α] (a b : α) : a ≤ a ⊔ b := by
  sorry

-- Exercise 17: a ⊓ (a ⊔ b) = a (absorption law)
example [Lattice α] (a b : α) : a ⊓ (a ⊔ b) = a := by
  sorry

-- Exercise 18: In a lattice, a ⊔ a = a
example [Lattice α] (a : α) : a ⊔ a = a := by
  sorry

/- ## Part 5: Monotone Functions -/

-- Exercise 19: The identity is monotone
example : Monotone (id : ℕ → ℕ) := by
  sorry

-- Exercise 20: The function n ↦ 2 * n is monotone on ℕ
example : Monotone (fun n : ℕ ↦ 2 * n) := by
  sorry

-- Exercise 21: If f and g are monotone, then f ∘ g is monotone
example [Preorder α] {β : Type*} [Preorder β] {γ : Type*} [Preorder γ]
    (f : β → γ) (g : α → β) (hf : Monotone f) (hg : Monotone g) :
    Monotone (f ∘ g) := by
  sorry

-- Exercise 22: A constant function is monotone
example [Preorder α] {β : Type*} [Preorder β] (c : β) :
    Monotone (fun _ : α ↦ c) := by
  sorry

/- ## Part 6: Complete Lattices -/

-- Exercise 23: ⊥ ≤ a for any a in a complete lattice
example [CompleteLattice α] (a : α) : ⊥ ≤ a := by
  sorry

-- Exercise 24: a ≤ ⊤ for any a in a complete lattice
example [CompleteLattice α] (a : α) : a ≤ ⊤ := by
  sorry

-- Exercise 25: If a ∈ s, then a ≤ sSup s
example [CompleteLattice α] (s : Set α) (a : α) (ha : a ∈ s) :
    a ≤ sSup s := by
  sorry

-- Exercise 26: sSup of the empty set is ⊥
example [CompleteLattice α] : sSup (∅ : Set α) = ⊥ := by
  sorry
