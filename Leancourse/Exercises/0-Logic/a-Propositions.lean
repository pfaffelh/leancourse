import Mathlib -- load everything, in particular tactics

/-!
# L-a -- Propositions and implication

*Logic block, week 1. No chapter of its own: the theory is Curry-Howard (1.5) and the axioms (2.2), both later.*

Only propositions here: `P`, `Q`, `R`, ... No numbers, no sets, no
functions. The only connective is `→`.

## Tactics introduced here

| tactic       | use it when                                  |
|--------------|----------------------------------------------|
| `trivial`    | the goal is `True`                           |
| `intro hP`   | goal `P → Q`: assume `P`, prove `Q`         |
| `exact hP`   | `hP` proves the goal                         |
| `assumption` | some hypothesis proves the goal              |
| `apply hPQ`  | `hPQ : P → Q`, goal `Q`: now prove `P`      |
| `revert hP`  | the opposite of `intro`                      |
-/

variable (P Q R S T : Prop)

/-! ## Statements and proofs

`example : ...` has no name. `lemma name : ...` and
`theorem name : ...` do.

After `:=` comes the proof. A *term proof* writes it down directly. A
*tactic proof* starts with `by`. We use tactic mode.

`True` holds by definition. `trivial` proves it. -/

example : True := by
  trivial

/-! ## `sorry`

`sorry` closes any goal without proving it. Lean warns each time
(`declaration uses 'sorry'`). It would even close `False`.

Your task on every sheet: make it `sorry`-free. -/

/-! ## `intro`, `exact`, `assumption`

`P → Q` says: if `P` holds, then `Q` holds. So to prove `⊢ P → Q`,
assume `P` and prove `Q`.

`intro hP` turns the goal `⊢ P → Q` into a hypothesis `hP : P` with
new goal `⊢ Q`.

`exact hP` closes a goal that `hP` proves. `assumption` searches the
hypotheses for one. -/

example : P → P := by
  intro hP
  exact hP

example : P → P := by
  intro hP
  assumption

/-! `intro h1 h2 h3` introduces several at once.

Lean writes `→`, not `=>`. Type it `\to` or `\r`.

The `variable` line declares `P`, ..., `T` once. No need to repeat
`P : Prop` in every statement.

`→` is also the function arrow. A proof of `P → Q` *is* a function
from proofs of `P` to proofs of `Q`
([Curry-Howard](https://en.wikipedia.org/wiki/Curry%E2%80%93Howard_correspondence)).
So the proof above is also a term: -/

example : P → P := by
  exact fun hP ↦ hP

-- Exercise 1) Assume `P`, then assume it again.
example : P → (P → P) := by
  sorry

-- Exercise 2) `hQ` stands before the colon, so it is already there.
example (hQ : Q) : P → Q := by
  sorry

-- Exercise 3) A hypothesis `hPQ : P → Q` applies to a proof of `P`:
-- write `hPQ hP`, like a function.
example : P → (P → Q) → Q := by
  sorry

/-! ## `apply`

Goal `⊢ Q`, hypothesis `hPQ : P → Q`. Then it suffices to prove `P`.
`apply hPQ` replaces the goal `Q` by `P`.

`exact h` needs `h` to prove the goal already. `apply h` needs `h` to
*end* in the goal, and leaves its premises as new goals. -/

example (hP : P) (hPQ : P → Q) : Q := by
  apply hPQ
  exact hP

/-! The same, in function style: -/

example (hP : P) (hPQ : P → Q) : Q := by
  exact hPQ hP

/-! `apply` also works where `exact` would: -/

example (hP : P) : P := by
  apply hP

-- Exercise 4) `apply` twice, or one line in function style.
example (hP : P) (hPQ : P → Q) (hQR : Q → R) : R := by
  sorry

-- Exercise 5) Transitivity as a statement of its own.
example : (P → Q) → (Q → R) → (P → R) := by
  sorry

-- Exercise 6) A puzzle. Not all hypotheses are needed. Find a path
-- from `T` to `R`.
example (hPQ : P → Q) (hQT : Q → T) (hQR : Q → R) (hRS : R → S)
    (hTP : T → P) (hRT : R → T) : T → R := by
  sorry

/-! ## `revert`

`revert` undoes `intro`. With `hP : P` in the context and goal `⊢ Q`,
`revert hP` removes `hP` and makes the goal `⊢ P → Q`. -/

example (hPQ : P → Q) (hP : P) : Q := by
  revert hP
  -- goal is now `⊢ P → Q`
  exact hPQ

/-! A premise left of `→` and a hypothesis in the context are the same
thing, seen from two sides. `revert` switches between them. -/

-- Exercise 7) Do not apply `h` to `hP`. The `revert` is there. Look
-- at the goal it leaves.
example (h : P → Q) (hP : P) : Q := by
  revert hP
  sorry

/-! ## Which statements hold?

Seeing that something is *not* provable is half the skill.

Exactly one of the next three cannot be proved. Prove the other two.
For that one, leave the `sorry` and replace the comment above it by a
sentence saying why no proof exists. -/

-- Exercise 8a)
example : P → Q → P := by
  sorry

-- Exercise 8b)
example : P → P → Q := by
  sorry

-- Exercise 8c)
example : P → Q → Q := by
  sorry

/-! ## Several premises

`P → Q → R` has no brackets. Lean reads it as `P → (Q → R)`. Given a
proof of `P` you get back an implication, still waiting for `Q`.

Hence `intro hP hQ` works on such a goal, and `h : P → Q → R` is
applied in two steps: `h hP hQ`. -/

example (h : P → Q → R) (hP : P) (hQ : Q) : R := by
  exact h hP hQ

-- Exercise 9) Supply the premises in the other order.
example (h : P → Q → R) (hQ : Q) : P → R := by
  sorry

-- Exercise 10) Both hypotheses need `P`. Use the proof of `P` twice.
example (h : P → Q → R) (hPQ : P → Q) : P → R := by
  sorry

-- Exercise 11) Nothing new. Only `intro`, `apply`, `exact`.
example : (P → Q → R) → (P → Q) → (P → R) := by
  sorry
