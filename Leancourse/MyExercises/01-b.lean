import Mathlib

variable (P Q R S T: Prop)

/-
  We will no learn about the _apply_tactics. If the goal is `⊢ Q`, and we have a hypothesis `P → Q`, we can close the goal if we can prove `P`, right? With _apply_, this transition is performed.
-/

example (hP : P) (hPQ : P → Q) : Q := by
  apply hPQ
  exact hP

/--  Side note: again, this is like evaluating functions. If we evaluate the function `hPQ` at `hP`, we this gives the result. -/
example (hP : P) (hPQ : P → Q) : Q := by
  exact hPQ hP

/-- Often, `apply` can be used instead of `exact`. The reason is that we also _apply_ the hypothesis to the goal.  -/
example (hP : P) : P := by
  apply hP

-- Exercise 1) This is almost like in the first example, and can either be solved by `apply` twice, or using `apply` with two arguments.
example (hP : P) (hPQ : P → Q) (hQR : Q → R) : R := by
  exact hQR (hPQ hP)

-- Exercise 2) A small puzzle...
example (hPQ : P → Q) (hQT : Q → T) (hQR : Q → R) (hRS : R → S) (hTP : T → P) (hRT : R → T) : ( T → R ) := by
  intro hT
  apply hQR
  apply hPQ
  apply hTP hT

/-- The proposition `P ↔ Q` is equivalent to `(P → Q) ∧ (Q → P)`. We can split it using `constructor`. We then have two goals and it is good practise to use an own bullet for each of them. -/

example (hPQ : P → Q) (hQP : Q → P) : (P ↔ Q) := by
  constructor
  · exact hPQ
  · exact hQP

-- Exercise 3) The same puzzle as above, but with a different goal:
example (hPQ : P → Q) (hQT : Q → T) (hQR : Q → R) (hRS : R → S) (hTP : T → P) (hRT : R → T) : ( P ↔ R )  := by
  constructor
  · intro hP
    apply hQR
    apply hPQ hP
  · intro hR
    apply hTP
    apply hRT hR

-- For the negation of `P`, abbreviated by `¬P`, we remark that `¬P` is by definition equivalent to `P → false`.

example : ¬P ↔ (P → False) := by
  constructor
  · intro h1 h2
    apply h1
    exact h2
  · intro h1
    exact h1

-- Exercise 4) Consider the following: If the goal is `¬P`, another `intro` helps, since this is equivalent to `P → False`.
example (hP : P) (hQ : Q) (hPQ : P → Q) : ¬Q → ¬ P := by
  intro h1 h2
  apply h1
  exact hPQ h2

/-- We already noted that proving theorems is like evaluating functions. In Lean, evaluating a function of two (or more) variables feels a bit special. Consider some function `f : (ℕ × ℝ) → ℂ`. For fixed `n : ℕ`, we would like to say that this is a function of type `ℝ → ℂ`. For this, and other reasons, in Lean we introduce this function as `f : ℕ → ℝ → ℂ`, and we understand that the bracketing is like `f : ℕ → (ℝ → ℂ)` if not stated otherwise. When we look at this, for `n : ℕ`, we have the type`f n : ℝ → ℂ`, i.e. evaluating `f` at its first coordinate automatically gives the correct type. In the next exercise, we find a first application of such an ` ⬝ → ⬝ → ⬝`.
-/

-- Exercise 5) If both, `P` and `¬P` hold, something cannot be right.
example : P → ¬P → False := by
  intro h1 h2
  apply h2
  exact h1
