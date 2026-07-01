import Mathlib

/-
# Well-foundedness and well-founded recursion -- solutions
-/

/- ## Part 1: Well-founded relations -/

example : WellFounded (· < · : ℕ → ℕ → Prop) := Nat.lt_wfRel.wf

example (n : ℕ) : Acc (· < ·) n := Nat.lt_wfRel.wf.apply n

/- ## Part 2: Well-founded recursion -/

def steps2 (n : Nat) : Nat :=
  if h : 2 ≤ n then 1 + steps2 (n - 2) else 0
termination_by n
decreasing_by omega

def bits (n : Nat) : Nat :=
  if h : 2 ≤ n then 1 + bits (n / 2) else 1
termination_by n
decreasing_by omega

#eval steps2 10   -- 5
#eval bits 100    -- 7

/- ## Part 3: The axiom footprint

No `sorry`, so no `sorryAx`; both are constructive (no
`Classical.choice`). -/

#print axioms steps2
#print axioms bits
