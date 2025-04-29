import Mathlib

variables (P Q R S T: Prop)

/-
  So far, the hypotheses used have always resulted from the transformation of existing hypotheses. However, this does not always have to be the case, because new hypotheses can be added, but these also have to be proven. Here we learn about and become familiar with `by_cases` and `have`.-/

/-
  The `by_cases` tactic exploits the _law of the excluded middle_. This states that every proposition must be either true or false (and that there is no third possibility). `by_cases h : P` adds the hypothesis `h : P ∨ ¬P` and displays the result of `cases' h`.-/

example : (P ∨ ¬P) := by
  by_cases h : P
  · left
    exact h
  · right
    exact h

-- Exercise 1) If `Q` follows from both, `P` and `¬P`, it should always hold.

example (hPQ : P → Q) (hnPQ : ¬P → Q) : Q := by
  sorry

-- Exercise 2) In this exercise, there is a point where we assume that `Q` is either true or not.
example : (P ∨ Q) ↔ (P ∨ (¬Q → P)) := by
  sorry

/-
  The following example is solved quite concisely, but the `exact` line is initially quite difficult to read.  -/

example (hPQ : P → Q) (hPnQ : P → ¬Q) : ¬P := by
  intro hP
  exact (hPnQ hP) (hPQ hP)

/-
  It would be easier to read if we first showed `Q` and then `¬Q`. We do this using the `have` tactic. This allows us to postulate any new hypotheses that we have to prove before they are available.-/

example (hPQ : P → Q) (hPnQ : P → ¬Q) : ¬P := by
  intro hP
  have hQ : Q
  · apply hPQ hP
  have hnQ : ¬Q
  · apply hPnQ hP
  exact hnQ hQ

-- Exercise 3) We can circumvent `by_cases` by using `have`.
example (hPQ : P → Q) (hnPQ : ¬P → Q) : Q := by
  have h : P ∨ ¬ P → Q := by
    sorry
  sorry

-- Exercise 4) Here, `have` can help, too.
example (hPQ : P → Q) (hQR : Q → R ) (hSR : S → R ) : (P → R) ∧ (S → R) := by
  have h : P → R := by
    sorry
  sorry

-- Exercise 5) I found the following task difficult to prove. Remember that `P → Q` is identical to `Q ∨ ¬P`. However, with a few applications of `have` it should work.

example : (((P → Q) → P) → P) := by
  sorry
