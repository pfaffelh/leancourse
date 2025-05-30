import Mathlib

variable (P Q R S T: Prop)

/- Here, we continue with some more exercises, and some more tactics. -/

/-
  We start with the statement: **False implies anything**.

  In fact, this statement is already implemented in `Lean`, which can be read [here](https://leanprover-community.github.io/mathlib4_docs/Init/Prelude.html#False.elim). (You might as well read further on that page.)
-/


example : (False) → P := by
  exact False.elim

/- However, there is also a tactic for that: `exfalso`. As you see, it does the same as applying `False.elim`. -/

example : (False) → P := by
  intro h
  exfalso
  exact h

-- Exercise 1) We know already that `¬P` means that `P` is false. In other words, this means that `P ↔ false` is then true. We now show this:
example (hnP : ¬P) : P ↔ False := by
  constructor
  · exact hnP
  · exact False.elim

-- Exercise 2) This is a bit more involved:
example (hnP : ¬P) (hQ : Q) : ( P ↔ ¬Q ) := by
  constructor
  · intro hP
    exfalso
    exact hnP hP
  · intro hnQ
    exfalso
    exact hnQ hQ

-- Exercise 3: If a hypothesis is true, every true statement follows:
example : P → True := by
  intro hP
  trivial

-- Exercise 4a) A statement is not true iff it is false.
example : ¬True ↔ False := by
  constructor
  · intro h
    apply h
    trivial
  · intro h
    exfalso
    exact h

-- Exercise 4b) A statement if not false iff it is true.
example : True ↔ ¬ False := by
  constructor
  · intro h
    intro g
    exact g
  · intro h
    trivial

-- Exercise 5) It is equivalent if a statement is true or follows from a true hypothesis. :
example : (True → P) ↔ P := by
  constructor
  · intro h
    apply h
    trivial
  · intro h₀ h₁
    exact h₀

-- Exercise 6) Here is a repetition using double negatiion.
example : P → ¬¬P := by
  intro hP h1
  exact h1 hP

/-
  Now we come to proofs by contradiction. If we have the goal `⊢ P` and want to prove it using contradiction, we add another hypothesis `¬P` and have to get a contradiction, i.e. we have to prove `False`. This is done using `by_contra h`.
-/

-- We show the reverse of Exercise 6:
example : ¬¬P → P := by
  intro h1
  by_contra h2
  apply h1
  exact h2


-- Exercise 7: The reverse direction is by contradiction!
example : (P → Q) ↔ (¬ Q → ¬ P) := by
  constructor
  · intro hPQ hnQ hP
    apply hnQ
    exact hPQ hP
  · intro h hP
    by_contra h'
    apply h h' hP
