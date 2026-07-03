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

/- ## Part 4: Proof irrelevance

`Prop` has a defining feature that the `Type` universes lack: any two
proofs of the same proposition are *equal* -- and equal *by
definition*, so `rfl` proves it.  This is *proof irrelevance*: for a
proposition we care only *that* it holds, never *which* proof we
have. -/

-- Any two proofs of the same proposition are equal.
example (p : Prop) (h1 h2 : p) : h1 = h2 := by
  sorry

-- Consequently, two elements of a subtype are equal as soon as their
-- underlying values agree -- the embedded proof is irrelevant.
example (n : ℕ) (h1 h2 : 0 < n) :
    (⟨n, h1⟩ : {m : ℕ // 0 < m}) = ⟨n, h2⟩ := by
  sorry

-- Proof irrelevance is baked into the kernel and costs no axiom.
-- After filling in the first proof, uncomment to confirm it reports
-- "does not depend on any axioms":
-- theorem proof_irrel_ex (p : Prop) (h1 h2 : p) : h1 = h2 := rfl
-- #print axioms proof_irrel_ex

-- Contrast: `Type` is NOT proof-irrelevant.  Two natural numbers are
-- not equal merely because they share a type, so this `rfl` fails
-- (uncomment to see the error):
-- example (a b : ℕ) : a = b := rfl
