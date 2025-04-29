import Mathlib

variable (P Q R S T: Prop)

/-
  Now we come to combining statements with `∧` and `∨`. These can occur in hypotheses and goals. Correspondingly, we have four cases which we have to deal with.
-/

/-
  We have already seen that if we have a goal `P ↔ Q`, we can use _constructor_ to create two goals for the two directions. The reason for this is that `P ↔ Q` is, by definition, equal to `(P → Q) ∧ (Q → P)`. The `constructor` tactic helps us for each such conjunction.
-/
example (hP : P) (hQ : Q) : P ∧ Q := by
  constructor
  · exact hP
  · exact hQ

-- Exercise 1) This is just one step more than above.
example (hP : P) (hQ : Q) (hR : R): P ∧ (Q ∧ R) := by
  sorry

/-
  The situation is a bit different if `P ∨ Q` is the goal. Here it is sufficient to show one of the two statements (`P` or `Q`). Accordingly, there are the tactics `left` and `right`, depending on whether the first or second goal is pursued.-/
example (hP : P) : P ∨ Q := by
  left
  exact hP

example (hQ : Q) : P ∨ Q := by
  right
  exact hQ

-- Exercise 2) If there are three statements connected by `∧`, then `P ∧ Q ∧ R` is implicitly put into brackets as `P ∧ (Q ∧ R)`. This should help to achieve this goal:
example (hQ : Q) : P ∨ Q ∨ R := by
  sorry

-- Exercise 3) Nested `constructor` tactics are possible as well.
example (hPQ : P → Q) (hQT : Q → T) (hQR : Q → R) (hRS : R → S) (hTP : T → P) (hRT : R → T) : ( (Q ↔ R) ∧ (R ↔ T)) := by
  sorry

/-
  If a `∧` or `∨` link occurs in a hypothesis, the `cases'` tactic helps.
  In the case of a `∧` in a hypothesis, two hypotheses arise. Since both must be valid, this is identical to the initial hypothesis.-/

example (hPQ : P ∧ Q) : P := by
  cases' hPQ with hP hQ
  exact hP

/-
  Incidentally, in a hypothesis `h : P ∧ Q` with `h.1` and `h.2`, one can directly access `P` and `Q`.-/

example (hPQ : P ∧ Q) : P := by
  exact hPQ.1

/-
  If the hypothesis is `h : P ↔ Q` (which is equivalent to `(P → Q) ∧ (Q → P)`=, we can also write `h.mp` (_modus ponens_, for the forward direction) and `h.mpr` (_modus ponens reverse_, for the backward direction):
-/
example (hP : P) (hPQ : P ↔ Q) : Q := by
  apply hPQ.mp
  exact hP

example (hQ : Q) (hPQ : P ↔ Q) : P := by
  apply hPQ.mpr
  exact hQ

/-
  With a hypothesis `h : P ∨ Q`, we have to prove the goal in two cases: if `P` holds, or if `Q` holds. With `cases' h` this is done. For the two remaining goals, one has the hypothesis `h : P`, while the other has `h : Q`.
-/
example (hPQ : P ∨ Q) : Q ∨ P := by
  cases' hPQ with hP hQ
  · right
    exact hP
  · left
    exact hQ

-- Exercise 4) A simple conclusion for `∧` and `∨`.
example : (P ∧ Q) → (P ∨ Q) := by
  sorry

-- Exercise 5) `P` and `¬P` cannot hold at the same time.
example : (P ∧ ¬P) ↔ false := by
  sorry

-- Exercise 6a) One of the deMorgan's rules for negation:
example : ¬(P ∨ Q) ↔ (¬P ∧ ¬ Q) := by
  sorry

-- Exercise 6b) Another deMorgan's rule for negation:
example : ¬(P ∧ Q) ↔ (¬P ∨ ¬ Q) := by
  sorry

-- Exercise 7a) Now we can prove deMorgan's rules for `∧` and `∨`. Here is the first:
example : P ∨ (Q ∧ R) ↔ (P ∨ Q) ∧ (P ∨ R) := by
  sorry


-- Exercise 7b) Here is the second:
example : P ∧ (Q ∨ R) ↔ (P ∧ Q) ∨ (P ∧ R) := by
  sorry
