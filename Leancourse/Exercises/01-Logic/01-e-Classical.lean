import Mathlib

/-!
# 01-e -- Classical logic

Up to here every statement was provable *constructively*: the proof
built the thing it claimed.

This sheet adds one principle: every proposition is either true or
false. That is the *law of the excluded middle*, `P ∨ ¬P`. It cannot
be proved from what we had. In Lean it is available, and the tactics
below use it.

Everything that was impossible on the earlier sheets becomes
possible here. That is the point: it marks exactly where classical
logic is needed.

## Tactics introduced here

| tactic          | use it when                                    |
|-----------------|------------------------------------------------|
| `by_cases h : P`| split into the case `h : P` and `h : ¬P`      |
| `Classical.em P`| the same, as a term `P ∨ ¬P`                  |
| `by_contra h`   | goal `⊢ P`: assume `h : ¬P`, derive `False`   |
| `push_neg`      | push `¬` inwards through `∧`, `∨`, `→`       |
-/

variable (P Q R S T : Prop)

/-! ## `by_cases`

`by_cases h : P` splits the proof in two. In the first goal
`h : P`, in the second `h : ¬P`. -/

example : P ∨ ¬P := by
  by_cases h : P
  · left
    exact h
  · right
    exact h

/-! The same statement as a term is `Classical.em P`: -/

example : P ∨ ¬P := by
  exact Classical.em P

-- Exercise 1) If `Q` follows in both cases, it holds.
example (hPQ : P → Q) (hnPQ : ¬P → Q) : Q := by
  sorry

-- Exercise 2) Case split on `Q`, not on `P`.
example : (P ∨ Q) ↔ (P ∨ (¬Q → P)) := by
  sorry

/-! ## `by_contra`

To prove `⊢ P` by contradiction, assume `¬P` and derive `False`.
`by_contra h` does that: it adds `h : ¬P` and makes the goal
`⊢ False`. -/

example : ¬¬P → P := by
  intro h1
  by_contra h2
  exact h1 h2

-- Exercise 3) Double negation, the other direction was 01-d.
example : ¬¬P ↔ P := by
  sorry

-- Exercise 4) The converse of 01-d exercise 9.
example : (P → Q) ↔ (¬Q → ¬P) := by
  sorry

-- Exercise 5) The De Morgan law that failed constructively.
example : ¬(P ∧ Q) ↔ (¬P ∨ ¬Q) := by
  sorry

-- Exercise 6) An implication is a disjunction in disguise.
example : (P → Q) ↔ (¬P ∨ Q) := by
  sorry

-- Exercise 7) Negating an implication.
example : ¬(P → Q) ↔ (P ∧ ¬Q) := by
  sorry

/-! ## `push_neg`

The exercises above are the rules for moving `¬` inwards. `push_neg`
applies them for you.

`¬(P ∧ Q)` becomes `P → ¬Q`, `¬(P ∨ Q)` becomes `¬P ∧ ¬Q`, `¬¬P`
becomes `P`, and `¬(P → Q)` becomes `P ∧ ¬Q`. -/

example (h : ¬(P ∨ Q)) : ¬P ∧ ¬Q := by
  push_neg at h
  exact h

/-! Without `at h` it works on the goal instead: -/

example (hP : P) (hnQ : ¬Q) : ¬(P → Q) := by
  push_neg
  exact ⟨hP, hnQ⟩

-- Exercise 8) One `push_neg`, then finish.
example (h : ¬(P → Q)) : P := by
  sorry

-- Exercise 9) A proposition implied by its own negation holds.
example : (¬P → P) → P := by
  sorry

/-! ## Peirce's law

The following is the classic example of a statement that uses only
`→` and is still not provable constructively. -/

-- Exercise 10) Start with `by_cases` on `P`.
example : ((P → Q) → P) → P := by
  sorry

-- Exercise 11) Equally classical, and shorter than it looks.
example : (P → Q) ∨ (Q → P) := by
  sorry

-- Exercise 12) A conclusion from both halves of a case split.
example (h1 : P → R) (h2 : ¬P → R) : R := by
  sorry
