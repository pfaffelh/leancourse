import Mathlib

/-
# Well-foundedness and well-founded recursion

Companion sheet to the *Well-Foundedness and Paradoxes* chapter.

A relation is *well-founded* when there are no infinite descending
chains; equivalently, every element is *accessible* (`Acc`).  Lean
uses this to justify recursion that is not structural, through the
`termination_by` / `decreasing_by` clauses.

Replace every `sorry` with a proof, and every `decreasing_by sorry`
with a terminating tactic.
-/

/- ## Part 1: Well-founded relations -/

-- `<` on `ℕ` is well-founded.  Mathlib already knows this; find the
-- right term (hint: `Nat.lt_wfRel`).
example : WellFounded (· < · : ℕ → ℕ → Prop) := by
  sorry

-- Every natural number is accessible under `<`.
-- (Hint: a `WellFounded` proof can be `.apply`-ed to an element.)
example (n : ℕ) : Acc (· < ·) n := by
  sorry

/- ## Part 2: Well-founded recursion

Each definition recurses on an argument that is *not* a structural
subterm, so Lean needs a termination proof.  The measure is given by
`termination_by`; supply the `decreasing_by` proof.  The goal is a
simple inequality about `ℕ` -- `omega` will close it. -/

-- How often can you subtract 2 before dropping below 2?
def steps2 (n : Nat) : Nat :=
  if h : 2 ≤ n then 1 + steps2 (n - 2) else 0
termination_by n
decreasing_by sorry

-- How often can you halve `n` before reaching 1 (roughly its number
-- of binary digits)?
def bits (n : Nat) : Nat :=
  if h : 2 ≤ n then 1 + bits (n / 2) else 1
termination_by n
decreasing_by sorry

-- Once both definitions go through, these should evaluate to 5 and 7:
-- #eval steps2 10
-- #eval bits 100

/- ## Part 3: The axiom footprint (exploration, no proof needed)

While a `sorry` is still present, `#print axioms steps2` lists
`sorryAx`.  After you have filled in the `decreasing_by` proofs,
uncomment the lines below: `sorryAx` should be gone, and you will see
`propext` and `Quot.sound` but *not* `Classical.choice` -- so these
functions are fully constructive. -/

-- #print axioms steps2
-- #print axioms bits
