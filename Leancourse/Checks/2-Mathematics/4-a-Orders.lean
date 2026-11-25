import Mathlib

/-
# (witness) 2.4-a -- Orders and lattices

*Notes chapter 2.4, week 13.*

These exercises cover lattices, monotone functions, complete lattices,
and the Knaster-Tarski fixed point theorem. The order on numbers and
the subset order are practised on sheets `2.0-a` and `2.2-a`.
One worked proof for each exercise.

Explanations and worked examples are in the course notes:
https://pfaffelh.github.io/leancourse/Mathematics/#orders-and-lattices
-/

variable {α : Type*}

/- ## Part 1: General Lattices -/

-- Exercise 1: In a lattice, a ⊔ b = b ⊔ a
example [Lattice α] (a b : α) : a ⊔ b = b ⊔ a := by
  exact sup_comm a b

-- Exercise 2: In a lattice, a ⊓ b = b ⊓ a
example [Lattice α] (a b : α) : a ⊓ b = b ⊓ a := by
  exact inf_comm a b

-- Exercise 3: a ≤ a ⊔ b
example [Lattice α] (a b : α) : a ≤ a ⊔ b := by
  exact le_sup_left

-- Exercise 4: a ⊓ (a ⊔ b) = a (absorption law)
example [Lattice α] (a b : α) : a ⊓ (a ⊔ b) = a := by
  exact inf_sup_self

-- Exercise 5: In a lattice, a ⊔ a = a
example [Lattice α] (a : α) : a ⊔ a = a := by
  exact sup_idem a

/- ## Part 2: Monotone Functions -/

-- Exercise 6: The identity is monotone
example : Monotone (id : ℕ → ℕ) := by
  exact monotone_id

-- Exercise 7: The function n ↦ 2 * n is monotone on ℕ
example : Monotone (fun n : ℕ ↦ 2 * n) := by
  intro m n h
  dsimp only
  omega

-- Exercise 8: If f and g are monotone, then f ∘ g is monotone
example [Preorder α] {β : Type*} [Preorder β] {γ : Type*} [Preorder γ]
    (f : β → γ) (g : α → β) (hf : Monotone f) (hg : Monotone g) :
    Monotone (f ∘ g) := by
  exact hf.comp hg

-- Exercise 9: A constant function is monotone
example [Preorder α] {β : Type*} [Preorder β] (c : β) :
    Monotone (fun _ : α ↦ c) := by
  exact monotone_const

-- Exercise 10: Taking complements is antitone: a larger set has a
-- smaller complement. Hint: `Set.compl_subset_compl`.
example : Antitone (fun s : Set ℕ ↦ sᶜ) := by
  intro s t h
  exact Set.compl_subset_compl.mpr h

/- ## Part 3: Complete Lattices -/

-- Exercise 11: ⊥ ≤ a for any a in a complete lattice
example [CompleteLattice α] (a : α) : ⊥ ≤ a := by
  exact bot_le

-- Exercise 12: a ≤ ⊤ for any a in a complete lattice
example [CompleteLattice α] (a : α) : a ≤ ⊤ := by
  exact le_top

-- Exercise 13: If a ∈ s, then a ≤ sSup s
example [CompleteLattice α] (s : Set α) (a : α) (ha : a ∈ s) :
    a ≤ sSup s := by
  exact le_sSup ha

-- Exercise 14: sSup of the empty set is ⊥
example [CompleteLattice α] : sSup (∅ : Set α) = ⊥ := by
  exact sSup_empty

/- ## Part 4: The Knaster-Tarski Fixed Point Theorem -/

-- Exercise 15: lfp f is a fixed point of f.
example [CompleteLattice α] (f : α →o α) :
    f (OrderHom.lfp f) = OrderHom.lfp f := by
  exact OrderHom.map_lfp f

-- Exercise 16: lfp is the least prefixed point:
-- if f a ≤ a, then lfp f ≤ a.
example [CompleteLattice α] (f : α →o α) (a : α) (h : f a ≤ a) :
    OrderHom.lfp f ≤ a := by
  exact OrderHom.lfp_le f h

-- Exercise 17: lfp is in particular the least fixed point.
example [CompleteLattice α] (f : α →o α) (a : α) (h : f a = a) :
    OrderHom.lfp f ≤ a := by
  exact OrderHom.lfp_le f h.le

-- Exercise 18: gfp f is a fixed point of f.
example [CompleteLattice α] (f : α →o α) :
    f (OrderHom.gfp f) = OrderHom.gfp f := by
  exact OrderHom.map_gfp f

-- Exercise 19: gfp is the greatest postfixed point.
example [CompleteLattice α] (f : α →o α) (a : α) (h : a ≤ f a) :
    a ≤ OrderHom.gfp f := by
  exact OrderHom.le_gfp f h

-- Exercise 20: lfp ≤ gfp.
example [CompleteLattice α] (f : α →o α) :
    OrderHom.lfp f ≤ OrderHom.gfp f := by
  exact (OrderHom.lfp_le f (OrderHom.map_gfp f).le).trans le_rfl

-- Exercise 21: For the identity OrderHom, lfp id = ⊥.
example [CompleteLattice α] :
    OrderHom.lfp (OrderHom.id : α →o α) = ⊥ := by
  exact le_antisymm (OrderHom.lfp_le _ le_rfl) bot_le

-- Exercise 22: For the identity OrderHom, gfp id = ⊤.
example [CompleteLattice α] :
    OrderHom.gfp (OrderHom.id : α →o α) = ⊤ := by
  exact le_antisymm le_top (OrderHom.le_gfp _ le_rfl)

-- Exercise 23: A monotone map on Set X has a fixed point.
-- (Just an existence statement.)
example {X : Type*} (f : Set X →o Set X) : ∃ A : Set X, f A = A := by
  exact ⟨OrderHom.lfp f, OrderHom.map_lfp f⟩

-- Exercise 24: If f a ≤ a, then iterating f keeps a as an upper bound.
example [CompleteLattice α] (f : α →o α) (a : α) (h : f a ≤ a) (n : ℕ) :
    f^[n] a ≤ a := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    exact (f.mono ih).trans h
