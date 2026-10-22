import Mathlib

/-!
# 08-a -- Puzzles

Three puzzles. All three need classical logic, and all three need
planning: work the proof out before you type it. No new tactic is
required -- `by_cases`, `by_contra`, `push Not`, `obtain`, `refine`
and `absurd` are enough.

A bonus sheet. Nothing later depends on it.

The first two puzzles are the last two levels of the Incredible Proof
Machine (Joachim Breitner, <https://incredible.pm>, MIT licence); the
third is Raymond Smullyan's.
-/

/-! ## The drinker paradox

In every pub there is a guest such that, if that guest drinks, then
everybody drinks.

The sentence sounds wrong until one reads the implication. Either
everybody drinks, and any guest will do; or somebody does not, and
that guest makes the implication vacuously true. The pub needs at
least one guest, which is what `[Inhabited α]` says: `default : α`. -/

-- Exercise 1) Start with `by_cases h : ∀ y, P y`.  In the second
--   case `push Not at h` produces a guest who does not drink.
example (α : Type) [Inhabited α] (P : α → Prop) : ∃ x, P x → ∀ y, P y := by
  sorry

/-! ## The hardest level

`R` is a predicate and `f` a function. The single hypothesis says
that whatever fails `R`, its image under `f` has it. Find an object
that satisfies `R` and whose image under `f` twice does too. -/

-- Exercise 2) Produce some `b` with `R b` first: either `default`
--   has it, or `f default` does.  Then split on `R (f (f b))`.
example (α : Type) [Inhabited α] (R : α → Prop) (f : α → α)
    (h : ∀ x, ¬R x → R (f x)) : ∃ x, R x ∧ R (f (f x)) := by
  sorry

/-! ## Knights and knaves

On Smullyan's island knights always tell the truth and knaves always
lie. A says: "We are both knaves." Write `A` for "A is a knight" and
`B` for "B is a knight". That A says the sentence means that A is a
knight exactly when the sentence is true. Show that A is a knave and
B a knight. -/

-- Exercise 3) Prove `¬A` first: assume `A` and apply `h.mp` to it.
example (A B : Prop) (h : A ↔ ¬A ∧ ¬B) : ¬A ∧ B := by
  sorry
