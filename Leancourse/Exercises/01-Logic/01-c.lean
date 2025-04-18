import Mathlib

variables (P Q R S T: Prop)

/-
  False implies anything.
-/
example (h : False) : P := by
  exfalso
  exact h

-- Exercise 1) We know already that `¬P` means that `P` is false. In other words, this means that `P ↔ false` is then true. We now show this:
example (hnP : ¬P) : P ↔ False := by
  sorry

-- Exercise 2) This is a bit more involved:
example (hnP : ¬P) (hQ : Q) : ( P ↔ ¬Q ) := by
  sorry

-- Exercise 3: If a hypothesis is true, every true statement follows:
example : P → True := by
  sorry

-- Exercise 4a) A statement is not true iff it is false.
example : ¬True ↔ False := by
  sorry

-- Exercise 4b) A statement if not false iff it is true.
example : True ↔ ¬ False := by
 sorry

-- Exercise 5) It is equivalent if a statement is true or follows from a true hypothesis. :
example : (True → P) ↔ P := by
  sorry

-- Exercise 6) Here is a repetition using double negatiion.
example : P ↔ ¬¬P := by
  sorry

/-
  Now we come to proofs by contradiction. If we have the goal `⊢ P` and want to prove it using contradiction, we add another hypothesis `¬P` and have to get a contradiction, i.e. we have to prove `false`.
-/

-- We show the reverse of Exercise 5:
example : ¬¬P → P := by
  intro h1
  by_contra h2
  apply h1
  exact h2

-- Exercise 7: At the reverse direction, an apply leads to two new goals.
example : (P → Q) ↔ (¬ Q → ¬ P) := by
  sorry
