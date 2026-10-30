import Mathlib

/-
# (witness) 2.4-a -- Orders and lattices

*Notes chapter 2.4, week 12.*

These exercises cover partial orders, lattices, and complete lattices.
You will work with ≤, ⊔, ⊓, sSup, and monotone functions.
One worked proof for each exercise.

Explanations and worked examples are in the course notes:
https://pfaffelh.github.io/leancourse/Mathematics/#orders-and-lattices
-/

variable {α : Type*}

/- ## Part 1: Partial Orders -/

-- Exercise 1: Transitivity of ≤ on ℕ
example (a b c : ℕ) (hab : a ≤ b) (hbc : b ≤ c) : a ≤ c := by
  exact le_trans hab hbc

-- Exercise 2: Antisymmetry of ≤ on ℕ
example (a b : ℕ) (hab : a ≤ b) (hba : b ≤ a) : a = b := by
  exact le_antisymm hab hba

-- Exercise 3: If a < b and b < c, then a < c
example (a b c : ℕ) (hab : a < b) (hbc : b < c) : a < c := by
  exact lt_trans hab hbc

-- Exercise 4: If a < b then a ≤ b
example (a b : ℕ) (h : a < b) : a ≤ b := by
  exact le_of_lt h

-- Exercise 5: If a ≤ b and a ≠ b, then a < b
example (a b : ℕ) (h : a ≤ b) (hne : a ≠ b) : a < b := by
  exact lt_of_le_of_ne h hne

/- ## Part 2: Sets and Subset Order -/

-- Exercise 6: Subset is reflexive
example (A : Set ℕ) : A ⊆ A := by
  exact subset_rfl

-- Exercise 7: Subset is transitive
example (A B C : Set ℕ) (hAB : A ⊆ B) (hBC : B ⊆ C) : A ⊆ C := by
  exact hAB.trans hBC

-- Exercise 8: If A ⊆ B and B ⊆ A, then A = B
example (A B : Set ℕ) (hAB : A ⊆ B) (hBA : B ⊆ A) : A = B := by
  exact Set.Subset.antisymm hAB hBA

/- ## Part 3: Lattice Operations on Sets -/

-- Exercise 9: A ⊆ A ∪ B
example (A B : Set ℕ) : A ⊆ A ∪ B := by
  exact Set.subset_union_left

-- Exercise 10: A ∩ B ⊆ A
example (A B : Set ℕ) : A ∩ B ⊆ A := by
  exact Set.inter_subset_left

-- Exercise 11: If A ⊆ C and B ⊆ C, then A ∪ B ⊆ C
example (A B C : Set ℕ) (hA : A ⊆ C) (hB : B ⊆ C) : A ∪ B ⊆ C := by
  exact Set.union_subset hA hB

-- Exercise 12: If C ⊆ A and C ⊆ B, then C ⊆ A ∩ B
example (A B C : Set ℕ) (hA : C ⊆ A) (hB : C ⊆ B) : C ⊆ A ∩ B := by
  exact Set.subset_inter hA hB

-- Exercise 13: Distributivity of ∩ over ∪
example (A B C : Set ℕ) : A ∩ (B ∪ C) = (A ∩ B) ∪ (A ∩ C) := by
  exact Set.inter_union_distrib_left A B C

/- ## Part 4: General Lattices -/

-- Exercise 14: In a lattice, a ⊔ b = b ⊔ a
example [Lattice α] (a b : α) : a ⊔ b = b ⊔ a := by
  exact sup_comm a b

-- Exercise 15: In a lattice, a ⊓ b = b ⊓ a
example [Lattice α] (a b : α) : a ⊓ b = b ⊓ a := by
  exact inf_comm a b

-- Exercise 16: a ≤ a ⊔ b
example [Lattice α] (a b : α) : a ≤ a ⊔ b := by
  exact le_sup_left

-- Exercise 17: a ⊓ (a ⊔ b) = a (absorption law)
example [Lattice α] (a b : α) : a ⊓ (a ⊔ b) = a := by
  exact inf_sup_self

-- Exercise 18: In a lattice, a ⊔ a = a
example [Lattice α] (a : α) : a ⊔ a = a := by
  exact sup_idem a

/- ## Part 5: Monotone Functions -/

-- Exercise 19: The identity is monotone
example : Monotone (id : ℕ → ℕ) := by
  exact monotone_id

-- Exercise 20: The function n ↦ 2 * n is monotone on ℕ
example : Monotone (fun n : ℕ ↦ 2 * n) := by
  intro m n h
  dsimp only
  omega

-- Exercise 21: If f and g are monotone, then f ∘ g is monotone
example [Preorder α] {β : Type*} [Preorder β] {γ : Type*} [Preorder γ]
    (f : β → γ) (g : α → β) (hf : Monotone f) (hg : Monotone g) :
    Monotone (f ∘ g) := by
  exact hf.comp hg

-- Exercise 22: A constant function is monotone
example [Preorder α] {β : Type*} [Preorder β] (c : β) :
    Monotone (fun _ : α ↦ c) := by
  exact monotone_const

/- ## Part 6: Complete Lattices -/

-- Exercise 23: ⊥ ≤ a for any a in a complete lattice
example [CompleteLattice α] (a : α) : ⊥ ≤ a := by
  exact bot_le

-- Exercise 24: a ≤ ⊤ for any a in a complete lattice
example [CompleteLattice α] (a : α) : a ≤ ⊤ := by
  exact le_top

-- Exercise 25: If a ∈ s, then a ≤ sSup s
example [CompleteLattice α] (s : Set α) (a : α) (ha : a ∈ s) :
    a ≤ sSup s := by
  exact le_sSup ha

-- Exercise 26: sSup of the empty set is ⊥
example [CompleteLattice α] : sSup (∅ : Set α) = ⊥ := by
  exact sSup_empty

/- ## Part 7: The Knaster-Tarski Fixed Point Theorem -/

-- Exercise 27: A fixed point of f.
-- If f a = a, then a is a fixed point.
example [CompleteLattice α] (f : α →o α) (a : α) (h : f a = a) :
    a = f a := by
  exact h.symm

-- Exercise 28: lfp f is a fixed point of f.
example [CompleteLattice α] (f : α →o α) :
    f (OrderHom.lfp f) = OrderHom.lfp f := by
  exact OrderHom.map_lfp f

-- Exercise 29: lfp is the least prefixed point:
-- if f a ≤ a, then lfp f ≤ a.
example [CompleteLattice α] (f : α →o α) (a : α) (h : f a ≤ a) :
    OrderHom.lfp f ≤ a := by
  exact OrderHom.lfp_le f h

-- Exercise 30: lfp is in particular the least fixed point.
example [CompleteLattice α] (f : α →o α) (a : α) (h : f a = a) :
    OrderHom.lfp f ≤ a := by
  exact OrderHom.lfp_le f h.le

-- Exercise 31: gfp f is a fixed point of f.
example [CompleteLattice α] (f : α →o α) :
    f (OrderHom.gfp f) = OrderHom.gfp f := by
  exact OrderHom.map_gfp f

-- Exercise 32: gfp is the greatest postfixed point.
example [CompleteLattice α] (f : α →o α) (a : α) (h : a ≤ f a) :
    a ≤ OrderHom.gfp f := by
  exact OrderHom.le_gfp f h

-- Exercise 33: lfp ≤ gfp.
example [CompleteLattice α] (f : α →o α) :
    OrderHom.lfp f ≤ OrderHom.gfp f := by
  exact (OrderHom.lfp_le f (OrderHom.map_gfp f).le).trans le_rfl

-- Exercise 34: For the identity OrderHom, lfp id = ⊥.
example [CompleteLattice α] :
    OrderHom.lfp (OrderHom.id : α →o α) = ⊥ := by
  exact le_antisymm (OrderHom.lfp_le _ le_rfl) bot_le

-- Exercise 35: For the identity OrderHom, gfp id = ⊤.
example [CompleteLattice α] :
    OrderHom.gfp (OrderHom.id : α →o α) = ⊤ := by
  exact le_antisymm le_top (OrderHom.le_gfp _ le_rfl)

-- Exercise 36: A monotone map on Set X has a fixed point.
-- (Just an existence statement.)
example {X : Type*} (f : Set X →o Set X) : ∃ A : Set X, f A = A := by
  exact ⟨OrderHom.lfp f, OrderHom.map_lfp f⟩

-- Exercise 37: If f a ≤ a, then iterating f keeps a as an upper bound.
example [CompleteLattice α] (f : α →o α) (a : α) (h : f a ≤ a) (n : ℕ) :
    f^[n] a ≤ a := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    exact (f.mono ih).trans h
