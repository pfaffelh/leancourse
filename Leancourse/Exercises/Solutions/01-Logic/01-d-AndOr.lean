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
  constructor
  · exact hP
  · constructor
    · exact hQ
    · exact hR

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
  right
  left
  exact hQ

-- Exercise 3) We already encountered nested `constructor` above. Here are some momre:
example (hPQ : P → Q) (hQT : Q → T) (hQR : Q → R) (hRS : R → S) (hTP : T → P) (hRT : R → T) : ( (Q ↔ R) ∧ (R ↔ T)) := by
  constructor
  · constructor
    · exact hQR
    · intro hR
      exact hPQ (hTP (hRT hR))
  · constructor
    · exact hRT
    · intro hT
      apply hQR
      apply hPQ (hTP hT)

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
  intro hPQ
  left
  exact hPQ.1

-- Exercise 5) `P` and `¬P` cannot hold at the same time.
example : (P ∧ ¬P) ↔ False := by
  constructor
  · intro h
    apply h.2 h.1
  · intro h
    cases' h

-- Exercise 6a) One of the deMorgan's rules for negation:
example : ¬(P ∨ Q) ↔ (¬P ∧ ¬ Q) := by
  constructor
  · intro h
    constructor
    · intro hP
      apply h
      left
      exact hP
    · intro hQ
      apply h
      right
      exact hQ
  · intro h hPQ
    cases' hPQ with h' h''
    · exact h.1 h'
    · exact h.2 h''

-- Exercise 6b) Another deMorgan's rule for negation:
example : ¬(P ∧ Q) ↔ (¬P ∨ ¬ Q) := by
  constructor
  · intro h
    by_cases hP : P
    · right
      intro hQ
      apply h
      constructor
      · exact hP
      · exact hQ
    · left
      exact hP
  · intro h h'
    cases' h with h1 h2
    · exact h1 h'.1
    · exact h2 h'.2

-- Exercise 7a) Now we can prove deMorgan's rules for `∧` and `∨`. Here is the first:
example : P ∨ (Q ∧ R) ↔ (P ∨ Q) ∧ (P ∨ R) := by
  constructor
  · intro h
    cases' h with h1 h2
    · constructor
      · left
        exact h1
      · left
        exact h1
    · constructor
      · right
        exact h2.1
      · right
        exact h2.2
  · intro h
    cases' h with hl hr
    cases' hl with hl1 hl2
    · left
      exact hl1
    · cases' hr with hr1 hr2
      · left
        exact hr1
      · right
        constructor
        · exact hl2
        · exact hr2

-- Exercise 7b) Here is the second:
example : P ∧ (Q ∨ R) ↔ (P ∧ Q) ∨ (P ∧ R) := by
  sorry
