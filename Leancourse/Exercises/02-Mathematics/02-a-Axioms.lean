import Mathlib

/-!
# 2.2-a -- The axioms of Lean

*Notes chapter 2.2, week 9.*

Lean's kernel is small. On top of it sit exactly three declared
axioms -- `propext`, `Quot.sound` and `Classical.choice` -- and
everything else is a theorem. This sheet puts each of them to work
and then uses `#print axioms` to see which ones a given proof
actually used.

Two surprises are worth the trouble: function extensionality is
*not* an axiom but a theorem (it follows from `Quot.sound`), and
neither is excluded middle (Diaconescu derives it from choice,
`propext` and `funext`).

## What is introduced here

| name                 | what it does                                 |
|----------------------|----------------------------------------------|
| `funext`             | two functions agreeing pointwise are equal   |
| `propext`            | two equivalent propositions are equal        |
| `Classical.em`       | `P ∨ ¬P`, for every `P`                      |
| `Classical.choice`   | turns `Nonempty α` into a term of `α`        |
| `Classical.choose`   | picks a witness out of an `∃`                |
| `noncomputable`      | marks a definition that cannot be run        |
| `#print axioms f`    | lists the axioms `f` depends on              |
-/

/-
## Part 1: Function extensionality

`funext` is a tactic and a theorem. It turns a goal `f = g` into
`∀ x, f x = g x`.
-/

-- Exercise 1: Two ways of writing the same function.
example : (fun n : ℕ => n + 0) = (fun n : ℕ => n) := by
  sorry

-- Exercise 2: The same, one level up -- functions into a function type.
example : (fun (m n : ℕ) => m + n) = (fun (m n : ℕ) => n + m) := by
  sorry

/-
## Part 2: Propositional extensionality

`propext : (a ↔ b) → a = b`. Two propositions that imply each other
are not merely equivalent, they are *equal*, and `rw` may replace
one by the other anywhere.
-/

-- Exercise 3: An equality of propositions, not an `↔`.
-- Hint: `propext`, or the `ext`-style lemma `iff_iff_eq`.
example : (True ∧ True) = True := by
  sorry

-- Exercise 4: Use `propext` to rewrite inside another proposition.
-- Hint: first prove `h : (P ∧ True) = P`, then `rw [h]`.
example (P : Prop) (hP : P) : (P ∧ True) := by
  sorry

/-
## Part 3: Excluded middle

`Classical.em P : P ∨ ¬P` holds for every `P`. Chapter 2.2 explains
that this is a *theorem*, not an axiom -- Diaconescu's argument
derives it from choice. Sheet `L-e` used it through `by_cases` and
`by_contra`; here it appears by name.
-/

-- Exercise 5: Double negation elimination.
example (P : Prop) : ¬¬P → P := by
  sorry

-- Exercise 6: One of de Morgan's laws that fails constructively.
example (P Q : Prop) : ¬(P ∧ Q) → (¬P ∨ ¬Q) := by
  sorry

/-
## Part 4: Choice

`Classical.choice : Nonempty α → α` is the one axiom that produces
*data*. `Nonempty α` only says that `α` has some element; choice
hands you one. Everything built with it is `noncomputable`.

`Classical.choose h` is the convenient form for `h : ∃ x, P x`, and
`Classical.choose_spec h` is the proof that the chosen witness has
the property.
-/

-- Exercise 7: From a bare existence proof to an actual term.
-- This is the direction that sheet `1.6-a` had to leave open.
noncomputable def existsToSubtype {α : Type} {P : α → Prop}
    (h : ∃ (x : α), P x) : {x : α // P x} :=
  sorry

-- Exercise 8: Skolemisation -- a family of existence proofs gives a
-- function. Hint: `Classical.choose` under a `fun n => ...`, or the
-- `choose` tactic.
example (h : ∀ (n : ℕ), ∃ (m : ℕ), m > n) :
    ∃ (f : ℕ → ℕ), ∀ n, f n > n := by
  sorry

-- Exercise 9: `Nonempty` is a `Prop`, so it carries no witness.
-- Going the easy way needs no axiom.
example {α : Type} (a : α) : Nonempty α := by
  sorry

/-
## Part 5: Reading the axiom footprint

`#print axioms f` lists the axioms the proof of `f` depends on.
A constructive proof depends on nothing; a classical one names
`Classical.choice`. This is the honest way to find out whether a
proof you wrote is constructive.
-/

-- Exercise 10: Prove this *without* any classical step, then
-- uncomment the `#print axioms` line: it must report that the
-- theorem does not depend on any axioms.
theorem contrapositive (P Q : Prop) (h : P → Q) : ¬Q → ¬P := by
  sorry

-- #print axioms contrapositive

-- Exercise 11: The converse needs excluded middle. Prove it, then
-- uncomment: the list should be
-- `[propext, Classical.choice, Quot.sound]` -- all three at once,
-- because excluded middle is derived from them.
theorem contrapositive_conv (P Q : Prop) (h : ¬Q → ¬P) : P → Q := by
  sorry

-- #print axioms contrapositive_conv

/-
## Part 6: What the kernel bakes in

Not everything that looks like an axiom is one. Proof irrelevance
and the computation rules are built into the kernel itself and cost
nothing -- sheet `2.3-a` looks at proof irrelevance in detail.
-/

-- Exercise 12: `rfl` proves this, so it needs no axiom at all.
-- Uncomment the `#print axioms` line afterwards to confirm.
theorem two_plus_two : (2 : ℕ) + 2 = 4 := by
  sorry

-- #print axioms two_plus_two
