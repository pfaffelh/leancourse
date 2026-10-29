import Mathlib

/-!
# (witness) L-e -- Classical logic

*Logic block, week 4. No chapter of its own: the theory is propositions as types (1.4) and the axioms (2.2), both later.*

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

| tactic           | use it when                                 |
|------------------|---------------------------------------------|
| `by_cases h : P` | split into the case `h : P` and `h : ¬P`    |
| `Classical.em P` | the same, as a term `P ∨ ¬P`                |
| `by_contra h`    | goal `⊢ P`: assume `h : ¬P`, derive `False` |
| `push Not`       | push `¬` inwards through `∧`, `∨`, `→`      |
| `contrapose`     | goal `P → Q`: prove `¬Q → ¬P` instead       |
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
  by_cases h : P
  · exact hPQ h
  · exact hnPQ h

-- Exercise 2) Case split on `Q`, not on `P`.
example : (P ∨ Q) ↔ (P ∨ (¬Q → P)) := by
  constructor
  · intro h
    obtain (hP | hQ) := h
    · left
      exact hP
    · right
      intro hnQ
      exact absurd hQ hnQ
  · intro h
    obtain (hP | hf) := h
    · left
      exact hP
    · by_cases hq : Q
      · right
        exact hq
      · left
        exact hf hq

/-! ## `by_contra`

To prove `⊢ P` by contradiction, assume `¬P` and derive `False`.
`by_contra h` does that: it adds `h : ¬P` and makes the goal
`⊢ False`. -/

example : ¬¬P → P := by
  intro h1
  by_contra h2
  exact h1 h2

-- Exercise 3) Double negation, the other direction was L-d.
example : ¬¬P ↔ P := by
  constructor
  · intro h
    by_contra h2
    exact h h2
  · intro hP hnP
    exact hnP hP

-- Exercise 4) The converse of L-d exercise 9.
example : (P → Q) ↔ (¬Q → ¬P) := by
  constructor
  · intro h hnQ hP
    exact hnQ (h hP)
  · intro h hP
    by_contra hq
    exact h hq hP

-- Exercise 5) The De Morgan law that failed constructively.
example : ¬(P ∧ Q) ↔ (¬P ∨ ¬Q) := by
  constructor
  · intro h
    by_cases hp : P
    · right
      intro hq
      exact h ⟨hp, hq⟩
    · left
      exact hp
  · intro h hpq
    obtain (hnP | hnQ) := h
    · exact hnP hpq.1
    · exact hnQ hpq.2

-- Exercise 6) An implication is a disjunction in disguise.
example : (P → Q) ↔ (¬P ∨ Q) := by
  constructor
  · intro h
    by_cases hp : P
    · right
      exact h hp
    · left
      exact hp
  · intro h hp
    obtain (hnP | hQ) := h
    · exact absurd hp hnP
    · exact hQ

-- Exercise 7) Negating an implication.
example : ¬(P → Q) ↔ (P ∧ ¬Q) := by
  constructor
  · intro h
    constructor
    · by_contra hnp
      apply h
      intro hp
      exact absurd hp hnp
    · intro hq
      apply h
      intro _
      exact hq
  · intro h himp
    exact h.2 (himp h.1)

/-! ## `push Not`

The exercises above are the rules for moving `¬` inwards. `push Not`
applies them for you.

`¬(P ∧ Q)` becomes `P → ¬Q`, `¬(P ∨ Q)` becomes `¬P ∧ ¬Q`, `¬¬P`
becomes `P`, and `¬(P → Q)` becomes `P ∧ ¬Q`. -/

example (h : ¬(P ∨ Q)) : ¬P ∧ ¬Q := by
  push Not at h
  exact h

/-! Without `at h` it works on the goal instead: -/

example (hP : P) (hnQ : ¬Q) : ¬(P → Q) := by
  push Not
  exact ⟨hP, hnQ⟩

-- Exercise 8) One `push Not`, then finish.
example (h : ¬(P → Q)) : P := by
  push Not at h
  exact h.1

-- Exercise 9) A proposition implied by its own negation holds.
example : (¬P → P) → P := by
  intro h
  by_cases hp : P
  · exact hp
  · exact h hp

/-! ## `contrapose`

Exercise 4 was `(P → Q) ↔ (¬Q → ¬P)`. `contrapose` applies that rule
to the goal: from `⊢ P → Q` it makes `⊢ ¬Q → ¬P`. -/

example (h : ¬Q → ¬P) : P → Q := by
  contrapose
  exact h

/-! `contrapose h` works on a hypothesis instead: `h : A` and goal
`⊢ B` become `h : ¬B` and goal `⊢ ¬A`.

`contrapose!` runs `push Not` on the result, which is almost always
what you want: -/

example (h : ¬(P ∧ Q)) : P → ¬Q := by
  contrapose! h
  exact h

-- Exercise 10) The direction of exercise 4 that needs `contrapose`.
example : (¬P → ¬Q) → (Q → P) := by
  intro h
  contrapose
  exact h

-- Exercise 11) With `contrapose!` this is two lines.
example (hnQ : ¬Q) (hPQ : P → Q) : ¬P := by
  contrapose! hnQ
  exact hPQ hnQ

/-! ## Peirce's law

The following is the classic example of a statement that uses only
`→` and is still not provable constructively. -/

-- Exercise 12) Start with `by_cases` on `P`.
example : ((P → Q) → P) → P := by
  intro h
  by_cases hp : P
  · exact hp
  · apply h
    intro hp2
    exact absurd hp2 hp

-- Exercise 13) Equally classical, and shorter than it looks.
example : (P → Q) ∨ (Q → P) := by
  by_cases hq : Q
  · left
    intro _
    exact hq
  · right
    intro hq2
    exact absurd hq2 hq

-- Exercise 14) A conclusion from both halves of a case split.
example (h1 : P → R) (h2 : ¬P → R) : R := by
  by_cases hp : P
  · exact h1 hp
  · exact h2 hp
