import Mathlib

/-!
# (witness) L-c -- Disjunction

*Logic block, week 2. No chapter of its own: the theory is propositions as types (1.3) and the axioms (2.2), both later.*

One connective: `∨`. Still only propositions.

Everything on this sheet is provable *constructively*: no case split
on "`P` or not `P`" is needed anywhere. That changes in L-e.

## Tactics introduced here

| tactic              | use it when                              |
|---------------------|------------------------------------------|
| `left`, `right`     | goal `P ∨ Q`: choose which side to prove |
| `Or.inl`, `Or.inr`  | the same, as terms                       |
| `obtain (h1 \| h2)` | `h : P ∨ Q`: split into two cases        |
-/

variable (P Q R S T : Prop)

/-! ## Proving an `∨`

`P ∨ Q` holds when at least one of them holds. So one of the two is
enough. `left` keeps the goal `⊢ P`, `right` keeps `⊢ Q`. -/

example (hP : P) : P ∨ Q := by
  left
  exact hP

example (hQ : Q) : P ∨ Q := by
  right
  exact hQ

/-! As terms: `Or.inl hP : P ∨ Q` and `Or.inr hQ : P ∨ Q`
(*in*troduce *l*eft / *r*ight). -/

example (hP : P) : P ∨ Q := by
  exact Or.inl hP

-- Exercise 1) `P ∨ Q ∨ R` means `P ∨ (Q ∨ R)`.
example (hQ : Q) : P ∨ Q ∨ R := by
  right
  left
  exact hQ

-- Exercise 2) Choose the other branch.
example (hR : R) : P ∨ Q ∨ R := by
  right
  right
  exact hR

/-! ## Using an `∨` hypothesis

`h : P ∨ Q` tells you one of them holds, not which. So you must
handle both cases.

`obtain (h1 | h2) := h` does that: it produces two goals, the first
with `h1 : P`, the second with `h2 : Q`. The bar `|` reads "or". -/

example (h : P ∨ Q) : Q ∨ P := by
  obtain (hP | hQ) := h
  · right
    exact hP
  · left
    exact hQ

-- Exercise 3) `∧` is stronger than `∨`.
example : (P ∧ Q) → (P ∨ Q) := by
  intro h
  left
  exact h.1

-- Exercise 4) Associativity, one direction.
example : (P ∨ Q) ∨ R → P ∨ (Q ∨ R) := by
  intro h
  obtain (h1 | hR) := h
  · obtain (hP | hQ) := h1
    · left
      exact hP
    · right
      left
      exact hQ
  · right
    right
    exact hR

-- Exercise 5) Both branches lead to the same conclusion.
example (hPR : P → R) (hQR : Q → R) : (P ∨ Q) → R := by
  intro h
  obtain (hP | hQ) := h
  · exact hPR hP
  · exact hQR hQ

-- Exercise 6) A disjunction can be weakened on both sides at once.
example (hPR : P → R) (hQS : Q → S) : (P ∨ Q) → (R ∨ S) := by
  intro h
  obtain (hP | hQ) := h
  · left
    exact hPR hP
  · right
    exact hQS hQ

/-! ## Distributivity

Two laws relating `∧` and `∨`. Both need a case split on the
hypothesis side. Work out which `obtain` to start with. -/

-- Exercise 7a)
example : P ∧ (Q ∨ R) ↔ (P ∧ Q) ∨ (P ∧ R) := by
  constructor
  · intro h
    obtain (hQ | hR) := h.2
    · left
      exact ⟨h.1, hQ⟩
    · right
      exact ⟨h.1, hR⟩
  · intro h
    obtain (h1 | h2) := h
    · exact ⟨h1.1, Or.inl h1.2⟩
    · exact ⟨h2.1, Or.inr h2.2⟩

-- Exercise 7b)
example : P ∨ (Q ∧ R) ↔ (P ∨ Q) ∧ (P ∨ R) := by
  constructor
  · intro h
    obtain (hP | hQR) := h
    · exact ⟨Or.inl hP, Or.inl hP⟩
    · exact ⟨Or.inr hQR.1, Or.inr hQR.2⟩
  · intro h
    obtain (hP | hQ) := h.1
    · left
      exact hP
    · obtain (hP | hR) := h.2
      · left
        exact hP
      · right
        exact ⟨hQ, hR⟩

-- Exercise 8) Commutativity of `∨`.
example : (P ∨ Q) ↔ (Q ∨ P) := by
  constructor
  · intro h
    obtain (hP | hQ) := h
    · right
      exact hP
    · left
      exact hQ
  · intro h
    obtain (hQ | hP) := h
    · right
      exact hQ
    · left
      exact hP

-- Exercise 9) Absorption.
example : P ∨ (P ∧ Q) ↔ P := by
  constructor
  · intro h
    obtain (hP | hPQ) := h
    · exact hP
    · exact hPQ.1
  · intro hP
    left
    exact hP
