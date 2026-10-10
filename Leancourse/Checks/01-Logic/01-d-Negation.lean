import Mathlib

/-!
# (witness) 01-d -- Negation, `False` and `True`

`¬P` is *by definition* `P → False`. Everything on this sheet follows
from that.

Still constructive: nothing here needs "`P` or not `P`". The laws
that do are in 01-e.

## Tactics introduced here

| tactic             | use it when                                 |
|--------------------|---------------------------------------------|
| `show`             | replace the goal by a definitionally equal one |
| `exfalso`          | give up on the goal, prove `False` instead  |
| `False.elim h`     | the same, as a term                         |
| `contradiction`    | the hypotheses are already contradictory    |
| `absurd hP hnP`    | `hP : P` and `hnP : ¬P` prove anything      |
-/

variable (P Q R S T : Prop)

/-! ## `¬P` is `P → False`

Nothing new is needed to prove a negation. The goal `⊢ ¬P` *is* the
goal `⊢ P → False`, so `intro` works on it. -/

example (h : P → False) : ¬P := by
  intro hP
  exact h hP

/-! `show` makes the identification visible. It replaces the goal by
one that is equal *by definition*. It changes nothing, but it
documents what you are doing. -/

example (h : P → False) : ¬P := by
  show P → False
  exact h

/-! `rfl` proves that both really are the same statement: -/

example : ¬P ↔ (P → False) := by
  rfl

-- Exercise 1) `P` and `¬P` cannot both hold.
example (hP : P) (hnP : ¬P) : False := by
  exact hnP hP

-- Exercise 2) Introduce twice.
example : P → ¬¬P := by
  intro hP hnP
  exact hnP hP

/-! ## `False` proves anything

`False` has no proof. So from a proof of `False` anything follows.

`exfalso` turns any goal into `⊢ False`. Use it when the hypotheses
are contradictory and the goal is irrelevant. -/

example (hP : P) (hnP : ¬P) : Q := by
  exfalso
  exact hnP hP

/-! The term version is `False.elim`: -/

example (h : False) : Q := by
  exact False.elim h

/-! `contradiction` does the search itself. It closes the goal if the
hypotheses contain `False`, or both `P` and `¬P`. -/

example (hP : P) (hnP : ¬P) : Q := by
  contradiction

/-! `absurd hP hnP` is the same as a term, for any goal: -/

example (hP : P) (hnP : ¬P) : Q := by
  exact absurd hP hnP

-- Exercise 3) Three ways to do this. Pick one.
example : False → P := by
  intro h
  exact False.elim h

-- Exercise 4) `¬P` says exactly that `P` is false.
example (hnP : ¬P) : P ↔ False := by
  constructor
  · intro hP
    exact hnP hP
  · intro h
    exact False.elim h

-- Exercise 5) Watch which hypothesis contradicts which.
example (hnP : ¬P) (hQ : Q) : P ↔ ¬Q := by
  constructor
  · intro hP
    exact absurd hP hnP
  · intro hnQ
    exact absurd hQ hnQ

/-! ## `True`

`True` holds always. `trivial` proves it. From anything, `True`
follows. -/

-- Exercise 6)
example : P → True := by
  intro _
  trivial

-- Exercise 7a)
example : ¬True ↔ False := by
  constructor
  · intro h
    exact h trivial
  · intro h
    exact False.elim h

-- Exercise 7b)
example : True ↔ ¬False := by
  constructor
  · intro _ h
    exact h
  · intro _
    trivial

-- Exercise 8) A hypothesis that always holds carries no information.
example : (True → P) ↔ P := by
  constructor
  · intro h
    exact h trivial
  · intro hP _
    exact hP

/-! ## Contraposition and De Morgan, constructive half

From `P → Q` you may always conclude `¬Q → ¬P`. The converse needs
more and waits for 01-e. -/

-- Exercise 9)
example (hPQ : P → Q) : ¬Q → ¬P := by
  intro hnQ hP
  exact hnQ (hPQ hP)

-- Exercise 10) One De Morgan law is constructive.
example : ¬(P ∨ Q) ↔ (¬P ∧ ¬Q) := by
  constructor
  · intro h
    constructor
    · intro hP
      exact h (Or.inl hP)
    · intro hQ
      exact h (Or.inr hQ)
  · intro h hor
    obtain (hP | hQ) := hor
    · exact h.1 hP
    · exact h.2 hQ

-- Exercise 11) Of the other law, only one direction is constructive.
-- This one.
example : (¬P ∨ ¬Q) → ¬(P ∧ Q) := by
  intro h hpq
  obtain (hnP | hnQ) := h
  · exact hnP hpq.1
  · exact hnQ hpq.2

-- Exercise 12) `P` and `¬P` never hold together.
example : ¬(P ∧ ¬P) := by
  intro h
  exact h.2 h.1
