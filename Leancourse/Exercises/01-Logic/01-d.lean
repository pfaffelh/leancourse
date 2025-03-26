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
  Ist die Hypothese h : P ↔ Q (was ja P → Q ∧ Q → P bedeutet), so kann man stattdessen auch h.mp und h.mpr anwenden:
-/
example (hP : P) (hPQ : P ↔ Q) : Q :=
begin
  apply hPQ.mp,
  exact hP,
end

example (hQ : Q) (hPQ : P ↔ Q) : P :=
begin
  apply hPQ.mpr,
  exact hQ,
end

/-
  Bei einer Verknüpfung h : P ∨ Q entstehen durch _cases_ zwei Ziele. Bei einem gilt P, bei der anderen Q. Da ja unter beiden Bedingungen das Ziel erreicht werden muss, ist dies identisch mit der Ausgangshypothese.
-/
example (hPQ : P ∨ Q) : Q ∨ P :=
begin
  cases hPQ with hP hQ,
  {
    right,
    exact hP,
  },
  {
    left,
    exact hQ,
  },
end

-- Aufgabe 4) Ein einfacher logischer Schluss.
example : (P ∧ Q) → (P ∨ Q) :=
begin
  sorry,
end

-- Aufgabe 5) P und ¬P können nicht gleichzeitig gelten...
example : (P ∧ ¬P) ↔ false :=
begin
  sorry,
end

-- Aufgabe 6a) eine deMorgan'sche Regel für die Negation:
example : ¬(P ∨ Q) ↔ (¬P ∧ ¬ Q) :=
begin
  sorry,
end


-- Aufgabe 6b) eine weitere deMorgan'sche Regel für die Negation:
example : ¬(P ∧ Q) ↔ (¬P ∨ ¬ Q) :=
begin
  sorry,
end

-- Aufgabe 7a) Jetzt könnten wir die deMorgan'schen Regeln für ∧ und ∨ beweisen. Hier die erste:
example : P ∨ (Q ∧ R) ↔ (P ∨ Q) ∧ (P ∨ R) :=
begin
  sorry,
end

-- Aufgabe 7b) Hier die zweite:
example : P ∧ (Q ∨ R) ↔ (P ∧ Q) ∨ (P ∧ R) :=
begin
  sorry,
end
