import Mathlib -- load everything, in particular tactics

-- These are names for all variables
variable (P Q R S T: Prop)

/-
With _intro_ you transform an assertion left of the first → intro a hypothesis and the remaining assertion is the new goal.
If the goal is identical to a hypothesis, _assumption_ closes the goal. Alternatively, you can use _exact_.
 -/

example : P → P := by
  intro hP
  assumption

example : P → P := by
  intro hP
  exact hP

/-
Here are some exercises: -/
-- Exercise 1) If `P`, then `P → P`.
-- Replace _sorry_ by appropriate tactics with _intro_ and _exact_.
example : P → (P → P) := by
  sorry

-- Exercise 2)
-- Here the proof starts with a hypothesis, which we do not have _intro_duced earlier.
example (hQ : Q) : (P → Q) := by
  sorry

-- Exercise 3) Why not try with `intros hP hPQ`. This shortens it a bit.
example : P → (P → Q) → Q := by
  sorry

-- Exercise 4) Make up your mind which of the following `examples` are valied, and prove them.
example : P → Q → P := by
  sorry

example : P → P → Q := by
  sorry

example : P → Q → Q := by
  sorry


/-
  We now use the _apply_-tactics. If the goal is `Q` and we have a hypothesis `P → Q`, we can close the goal if we can prove `P`, right? With _apply_ führen wir diese Operation durch.
-/
example (hP : P) (hPQ : P → Q) : Q := by
  apply hPQ
  exact hP

-- Nebenbei bemerkt geht das auch so: Man setze hP in hPQ ein, genauso wie man Funktionen hintereinander ausführen kann:
example (hP : P) (hPQ : P → Q) : Q := by
  exact hPQ hP

-- Oft kann man übrigens _apply_ statt _exact_ verwenden. Der Grund ist, dass man auch hier die Hypothese auf das Ziel anwendet.
example (hP : P) : P := by
  apply hP

-- Aufgabe 1) Das ist fast so wie im ersten Beispiel oben, und kann entweder durch zwei Anwendungen von _apply_ oder das Einsetzen zweier Funktionen gelöst werden:
example (hP : P) (hPQ : P → Q) (hQR : Q → R) : R := by
  sorry

-- Aufgabe 2) Ein kleines Labyrinth...
example (hPQ : P → Q) (hQT : Q → T) (hQR : Q → R) (hRS : R → S) (hTP : T → P) (hRT : R → T) : ( T → R ) := by
  sorry

-- Aus dem Ziel P ↔ Q erzeugt man mit _split_ zwei Ziele. Diese sind dann der Reihe nach abzuarbeiten:
example (hPQ : P → Q) (hQP : Q → P) : (P ↔ Q) := by
  split
  exact hPQ
  exact hQP

-- Aufgabe 3) Dasselbe Labyrinth wie oben, aber mit einem anderen Ziel.
example (hPQ : P → Q) (hQT : Q → T) (hQR : Q → R) (hRS : R → S) (hTP : T → P) (hRT : R → T) : ( P ↔ R )  := by
  sorry

-- Für die Negation von P, also ¬P, bemerken wir, dass ¬P definitorisch äquivalent ist zu P → false.
example : (¬ P ↔ (P → false)) := by
  constructor
  · intro h1 h2
    apply h1
    exact h2
  · intro h1
    exact h1

-- Aufgabe 4) Man beachte: Ist das Ziel ¬P, so führt ein weiteres _intro_ weiter, da das Ziel als P → false definiert ist.
example (hP : P) (hQ : Q) (hPQ : P → Q) : ¬Q → ¬ P := by
  sorry

-- Aufgabe 5) Gelten sowohl P als auch ¬P, kann etwas nicht stimmen.
example : P → ¬P → false := by
  sorry
