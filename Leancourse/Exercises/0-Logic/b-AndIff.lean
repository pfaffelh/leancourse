import Mathlib

/-!
# L-b -- Conjunction and biconditional

*Logic block, week 2. No chapter of its own: the theory is propositions as types (1.3) and the axioms (2.2), both later.*

Two connectives: `∧` and `↔`. Still only propositions.

## Tactics introduced here

| tactic            | use it when                               |
|-------------------|-------------------------------------------|
| `constructor`     | goal `P ∧ Q` or `P ↔ Q`: split into two   |
| `⟨hP, hQ⟩`        | the same, as a term                       |
| `h.1`, `h.2`      | `h : P ∧ Q`: take the parts               |
| `h.mp`, `h.mpr`   | `h : P ↔ Q`: take one direction           |
| `obtain ⟨hP, hQ⟩` | `h : P ∧ Q`: split it into two hypotheses |
-/

variable (P Q R S T : Prop)

/-! ## `constructor` on `∧`

`P ∧ Q` holds when both hold. Goal `⊢ P ∧ Q`: `constructor` gives two
goals, `⊢ P` and `⊢ Q`.

Use a bullet `·` for each goal. Type it `\.`. Bullets are not
required, but without them the two proofs run together. -/

example (hP : P) (hQ : Q) : P ∧ Q := by
  constructor
  · exact hP
  · exact hQ

/-! The anonymous constructor `⟨_, _⟩` does the same in one term. Type
the brackets `\<` and `\>`. -/

example (hP : P) (hQ : Q) : P ∧ Q := by
  exact ⟨hP, hQ⟩

-- Exercise 1) `P ∧ Q ∧ R` means `P ∧ (Q ∧ R)`.
example (hP : P) (hQ : Q) (hR : R) : P ∧ (Q ∧ R) := by
  sorry

-- Exercise 2) The same, as a single term. `⟨hP, hQ, hR⟩` nests.
example (hP : P) (hQ : Q) (hR : R) : P ∧ Q ∧ R := by
  sorry

/-! ## Using an `∧` hypothesis

`h : P ∧ Q` gives `h.1 : P` and `h.2 : Q`. -/

example (h : P ∧ Q) : P := by
  exact h.1

/-! `obtain ⟨hP, hQ⟩ := h` splits `h` into two named hypotheses
instead. Use it when you need both parts more than once. -/

example (h : P ∧ Q) : Q ∧ P := by
  obtain ⟨hP, hQ⟩ := h
  exact ⟨hQ, hP⟩

-- Exercise 3) Commutativity of `∧`.
example : (P ∧ Q) → (Q ∧ P) := by
  sorry

-- Exercise 4) Associativity, one direction.
example : (P ∧ Q) ∧ R → P ∧ (Q ∧ R) := by
  sorry

-- Exercise 5) Drop a conjunct.
example (h : P ∧ Q) (hPR : P → R) : R := by
  sorry

/-! ## `↔`

`P ↔ Q` is *by definition* `(P → Q) ∧ (Q → P)`. So `constructor`
splits it too: first goal `⊢ P → Q`, second `⊢ Q → P`. -/

example (hPQ : P → Q) (hQP : Q → P) : P ↔ Q := by
  constructor
  · exact hPQ
  · exact hQP

/-! From `h : P ↔ Q` take `h.mp : P → Q` (*modus ponens*) and
`h.mpr : Q → P` (*modus ponens reversed*). `h.1` and `h.2` work too. -/

example (hP : P) (h : P ↔ Q) : Q := by
  exact h.mp hP

-- Exercise 6) The other direction.
example (hQ : Q) (h : P ↔ Q) : P := by
  sorry

-- Exercise 7) Symmetry of `↔`.
example (h : P ↔ Q) : Q ↔ P := by
  sorry

-- Exercise 8) Transitivity of `↔`.
example (h1 : P ↔ Q) (h2 : Q ↔ R) : P ↔ R := by
  sorry

-- Exercise 9) `↔` really is a conjunction of two implications.
example : (P ↔ Q) ↔ ((P → Q) ∧ (Q → P)) := by
  sorry

-- Exercise 10) The puzzle from L-a, with a new goal.
example (hPQ : P → Q) (hQT : Q → T) (hQR : Q → R) (hRS : R → S)
    (hTP : T → P) (hRT : R → T) : Q ↔ R := by
  sorry

-- Exercise 11) `∧` distributes over `↔` in this sense.
example (h : P ↔ Q) : (P ∧ R) ↔ (Q ∧ R) := by
  sorry
