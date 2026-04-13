import Mathlib

/-
# Exercises 05-a: The Curry-Howard Correspondence

In these exercises, you will practice writing term-mode proofs (without tactics)
and compare them with tactic proofs. The goal is to see the Curry-Howard
correspondence in action: proofs are programs, propositions are types.
-/

variable (P Q R S : Prop)

/-
## Part 1: Term-mode proofs for basic logic

For each exercise, write a proof WITHOUT using `by` (i.e., a pure term-mode proof).
Recall:
  - Implication `P → Q` corresponds to function type
  - `fun h => ...` constructs a function (= proves an implication)
  - Function application `f x` applies a proof (= modus ponens)
  - `⟨a, b⟩` constructs a pair (= proves a conjunction)
  - `.1` and `.2` are projections (= eliminate a conjunction)
  - `Or.inl` and `Or.inr` inject into a disjunction
-/

-- Exercise 1: Identity (the simplest function)
example : P → P :=
  sorry

-- Exercise 2: Constant function (weakening)
example : P → Q → P :=
  sorry

-- Exercise 3: Function composition (transitivity of implication)
example : (P → Q) → (Q → R) → P → R :=
  sorry

-- Exercise 4: Pair construction (conjunction introduction)
example (hP : P) (hQ : Q) : P ∧ Q :=
  sorry

-- Exercise 5: First projection (conjunction elimination)
example (h : P ∧ Q) : P :=
  sorry

-- Exercise 6: Flip a conjunction
example : P ∧ Q → Q ∧ P :=
  sorry

-- Exercise 7: Left injection (disjunction introduction)
example (hP : P) : P ∨ Q :=
  sorry

-- Exercise 8: Case analysis on a disjunction
-- Hint: use Or.elim or the .elim method
example : P ∨ Q → (P → R) → (Q → R) → R :=
  sorry

-- Exercise 9: Flip a disjunction
example : P ∨ Q → Q ∨ P :=
  sorry

-- Exercise 10: Distribution of ∧ over ∨
example : P ∧ (Q ∨ R) → (P ∧ Q) ∨ (P ∧ R) :=
  sorry

/-
## Part 2: Negation as function to False

Recall that `¬P` is defined as `P → False`, and `False.elim` derives
anything from `False`.
-/

-- Exercise 11: Modus tollens (term-mode)
example : (P → Q) → ¬Q → ¬P :=
  sorry

-- Exercise 12: Contradiction yields anything
example : P → ¬P → Q :=
  sorry

-- Exercise 13: A logical equivalence
example : ¬(P ∨ Q) → ¬P ∧ ¬Q :=
  sorry

/-
## Part 3: Side-by-side comparison

For each exercise below, TWO proofs are requested: one in tactic mode and
one in term mode. Fill in both.
-/

-- Exercise 14a: Tactic proof
example : (P → Q) → (P → R) → P → Q ∧ R := by
  sorry

-- Exercise 14b: Term proof (same statement)
example : (P → Q) → (P → R) → P → Q ∧ R :=
  sorry

-- Exercise 15a: Tactic proof
example : P ∧ (Q ∧ R) → (P ∧ Q) ∧ R := by
  sorry

-- Exercise 15b: Term proof
example : P ∧ (Q ∧ R) → (P ∧ Q) ∧ R :=
  sorry

/-
## Part 4: Quantifiers as dependent types

Recall:
  - `∀ (x : α), P x` is a dependent function type (Pi type)
  - A proof is a function: `fun x => ...`
  - `∃ (x : α), P x` is an existential (proof-irrelevant Sigma)
  - A proof is a pair: `⟨witness, proof⟩`
-/

-- Exercise 16: A universal statement (term-mode)
-- Hint: fun n => ... where you provide a proof for each n
example : ∀ (n : ℕ), n + 0 = n :=
  sorry

-- Exercise 17: An existential statement (term-mode)
-- Hint: ⟨witness, proof⟩
example : ∃ (n : ℕ), n * n = 16 :=
  sorry

-- Exercise 18: From universal to existential (term-mode)
-- Hint: use the universal hypothesis at a specific point
example (h : ∀ (n : ℕ), n < n + 1) : ∃ (n : ℕ), n < n + 1 :=
  sorry

-- Exercise 19: Combining quantifiers (term-mode)
example : (∀ (n : ℕ), P → n = n) :=
  sorry

-- Exercise 20: A more complex existential
-- Prove that there exists a natural number that is both greater than 10
-- and less than 15.
example : ∃ (n : ℕ), n > 10 ∧ n < 15 :=
  sorry

/-
## Part 5: Challenge problems

These are harder. Use any proof style you like.
-/

-- Exercise 21: Curry-Howard for iff
-- `P ↔ Q` is `(P → Q) ∧ (Q → P)`, so a proof is a pair of functions
example : (P ↔ Q) → (Q ↔ R) → (P ↔ R) :=
  sorry

-- Exercise 22: A dependent function
-- Define a function that takes a natural number n and returns a proof
-- that n + n is even (divisible by 2).
example : ∀ (n : ℕ), ∃ (k : ℕ), n + n = 2 * k :=
  sorry

-- Exercise 23: The type of proofs is a function type
-- This exercise asks you to construct an element of a function type,
-- which IS a proof of an implication. Reflect on this duality.
def modusPonens : (P → Q) → P → Q :=
  sorry

-- Exercise 24: Flip function = commutativity of conjunction in disguise
def flip' (f : P → Q → R) : Q → P → R :=
  sorry
