import Mathlib

/-
# (witness) 2.3-a -- Well-foundedness and paradoxes

*Notes chapter 2.3, week 9.*
-/

/- ## Part 1: Accessibility -/

-- Exercise 1
example : Acc (· < ·) (0 : ℕ) := by
  constructor
  intro y hy
  omega

-- Exercise 2
example : Acc (· < ·) (1 : ℕ) := by
  constructor
  intro y hy
  have : y = 0 := by omega
  subst this
  constructor
  intro z hz
  omega

-- Exercise 3
example (n : ℕ) : Acc (· < ·) n := Nat.lt_wfRel.wf.apply n

-- Exercise 4
example : ¬ WellFounded (· > · : ℕ → ℕ → Prop) := by
  intro h
  obtain ⟨a, -, ha⟩ := h.has_min Set.univ ⟨0, trivial⟩
  exact ha (a + 1) trivial (by omega)

/- ## Part 2: Well-founded induction -/

def steps2 (n : Nat) : Nat :=
  if h : 2 ≤ n then 1 + steps2 (n - 2) else 0

-- Exercise 5
example (n : ℕ) : 2 * steps2 n ≤ n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rw [steps2]
    split_ifs with h
    · have := ih (n - 2) (by omega)
      omega
    · omega

/- ## Part 3: Self-membership and the diagonal -/

def mySet : Set ℕ := {0}
#check_failure (mySet ∈ mySet)

-- Exercise 6
example : ({0} : Set ℕ) ∈ ({{0}} : Set (Set ℕ)) := by
  rfl

-- Exercise 7
example {α : Type*} (r : α → α → Prop) :
    ¬ ∃ a, ∀ x, r x a ↔ ¬ r x x := by
  rintro ⟨a, ha⟩
  have h := ha a
  by_cases hr : r a a
  · exact h.mp hr hr
  · exact hr (h.mpr hr)

-- Exercise 8
example {α : Type*} (f : α → Set α) :
    ¬ Function.Surjective f := by
  intro hf
  obtain ⟨a, ha⟩ := hf {x | x ∉ f x}
  have h : a ∈ f a ↔ a ∉ f a := Set.ext_iff.mp ha a
  by_cases ha' : a ∈ f a
  · exact h.mp ha' ha'
  · exact ha' (h.mpr ha')
