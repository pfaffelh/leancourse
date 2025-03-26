import Mathlib -- load everything, in particular tactics

/-- We start by studying `Prop`-types. These are like mathematical theorems, i.e. can be either true or false. We start by introducing a bunch of variables which are generic propositions.-/

variable (P Q R S T: Prop)

/-- Apart from these types, we will in this and the upcoming exercises mostly deal with implications, i.e. Types of the form `P → Q`.-/

/- Let's start simple. -/

example : True := by
  triv

/-- Some remark:
* In Lean, we have `example` (which does not need an own name), `lemma` and `theorem` (both of which have a name). So, `example` is always followed by `:` while we have `lemma <nameOfLemma> : ` and `theorem <nameOfTheorem> :` for the latter two.
* The proof of the `True`-statement is right of `:=`. In principle, there are two types of proofs: term-proofs, and tyctic proofs. We will only deal with tactic proofs, which always start with the `by` keyword.
* Here, `triv` is a tactic, and has the only task of showing `True`. -/

/-
With _intro_ you transform an assertion left of the first → intro a hypothesis and the remaining assertion is the new goal. If the goal is identical to a hypothesis, _assumption_ closes the goal. Alternatively, you can use _exact_.
 -/

example : P → P := by
  intro hP
  assumption

example : P → P := by
  intro hP
  exact hP

/-- Note that the lean syntax does not use the usual double arrow `=>` here, but a single `→`. (Hover over the symbol in vscode in order to learn how to type it.) -/

/-- Side note: the `→` looks like a function application, doesn't it? In fact, theoretical computer scientists have shown that there is a close connection between applying functions and proving theorems; see [Curry-Howard correspondance](https://en.wikipedia.org/wiki/Curry%E2%80%93Howard_correspondence). This is why the proof could as well look like this: -/

example : P → P := by
  exact fun x ↦ x

/-- Here are some exercises. In all of them, we use the `sorry` axiom/tactics to get started. This tactics closes every goal (no matter if it is true or not). Of course, using `sorry` is like cheating, so your task is to make the exercises `sorry`-free.-/

/-- The statement `⊢ P → Q` (i.e. `P` implies `Q`) means that `Q` is valid if one may assume that the hypothesis `P` is correct. This transition from `⊢ P → Q` to the hypothesis `hP : P` with target `⊢ Q` is done using `intro hP`. Several `intro` commands can be abbreviated using `intro h1 h2...`.

If the hypothesis `hP : P` holds and we want to prove `⊢ P`, then we just have to apply `hP` to the goal. If goal and hypothesis are identical, this is done with `exact hP`. In a more general way, `assumption` searches all hypotheses for those that are identical with the goal by definition.-/

-- Exercise 1)
example : P → (P → P) := by
  sorry

-- Exercise 2)
-- Here the proof starts with a hypothesis, which we do not have _intro_duced earlier.
example (hQ : Q) : (P → Q) := by
  sorry

-- Exercise 3) Why not try with `intro hP hPQ`. This shortens it a bit.
example : P → (P → Q) → Q := by
  sorry

-- Exercise 4) Make up your mind which of the following `examples` are valid, and prove them.
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
