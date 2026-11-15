import Mathlib

/-!
# (witness) L-g -- Search and automation

*Logic block, week 5. No chapter of its own: the theory is propositions as types (1.4) and the axioms (2.3), both later.*

Everything on sheets a to f can also be done by machine. This sheet
shows how, and where the limits are.

Doing it by hand first was not wasted: when a tactic fails you need
to know what it was trying to do.

## Tactics introduced here

| tactic          | use it when                                                |
|-----------------|------------------------------------------------------------|
| `apply?`        | some lemma reduces the goal                                |
| `tauto`         | the goal is a tautology of propositional logic             |
| `itauto`        | the same, but *constructively*                             |
| `simp only [h]` | `simp` with only the lemmas named                          |
| `simp_all`      | `simp` on the goal and all hypotheses at once              |
| `simpa using h` | `simp` on the goal and on `h`, then close the goal by `h`  |
| `grind`         | the goal is "obvious" and mixes several kinds of reasoning |

## Tactics from earlier sheets

| sheet   | tactics  |
|---------|----------|
| `L-a`   | `exact`  |
| `L-f`   | `refine` |
| `1.1-c` | `exact?` |
-/

variable (P Q R S T : Prop)

/-! ## `apply?`

`exact?` (sheet `1.1-c`) reports only lemmas that close the goal.
`apply?` also reports lemmas that leave goals behind, written as
`refine lemma ?_` with the remaining goals underneath. The list is
long, and the first entry is often not the useful one: pick one whose
remaining goals you can prove.

Here `exact?` fails. Uncomment `apply?` and look for `Or.inr`: -/

example (hq : Q) (hr : R) : P ∨ (Q ∧ R) := by
  -- apply?
  refine Or.inr ?_
  exact ⟨hq, hr⟩

/-! Like `exact?`, `apply?` is slow. Replace it by the line you chose. -/

-- Exercise 1) `exact?` fails. Use `apply?`, pick a suggestion, and
-- finish the proof.
example (hp : P) (hq : Q) : (P ∧ Q) ∨ R := by
  refine Or.inl ?_
  exact ⟨hp, hq⟩

/-! ## `tauto`

`tauto` proves any tautology of propositional logic. Most of sheets
a to f fall to it. -/

example : ((P → Q) → P) → P := by
  tauto

-- Exercise 2) One line each.
example : ¬(P ∧ Q) ↔ (¬P ∨ ¬Q) := by
  tauto

-- Exercise 3)
example : P ∨ (Q ∧ R) ↔ (P ∨ Q) ∧ (P ∨ R) := by
  tauto

/-! ## `itauto`

`itauto` is `tauto` restricted to *constructive* reasoning: it never
uses `P ∨ ¬P`.

So the two tactics disagree exactly on the statements that need
classical logic. That is a test you can run yourself. -/

example : ¬(P ∨ Q) ↔ (¬P ∧ ¬Q) := by
  itauto

/-! The following needs the excluded middle, so `itauto` fails on it
while `tauto` succeeds. Swap the two and see: -/

example : ¬(P ∧ Q) ↔ (¬P ∨ ¬Q) := by
  tauto

/-! ## `simp`

`simp` rewrites with a large set of lemmas marked `@[simp]`, over and
over, until nothing changes. -/

example : (P ∧ True) ↔ P := by
  simp

/-! `simp` is convenient and fragile. Which lemmas carry the `@[simp]`
attribute changes between Mathlib versions, so a proof that is just
`simp` can break later. In a proof meant to last, prefer `simp only
[...]` with the lemmas named: -/

example : (P ∧ True) ↔ P := by
  simp only [and_true]

-- Exercise 4) `simp`, then the same with `simp only` and named
-- lemmas. Use `simp?` to find out which it used.
example : (P ∨ False) ↔ P := by
  simp only [or_false]

/-! ## `simp_all`

`simp` works on the goal. `simp_all` works on the goal *and* every
hypothesis, and repeats until nothing changes, feeding simplified
hypotheses back in. -/

example (h1 : P ∧ True) (h2 : P → Q) : Q ∧ True := by
  simp_all

-- Exercise 5) `simp` alone does not close this; `simp_all` does.
example (h1 : P ∨ False) (h2 : ¬Q → ¬P) : Q ∨ False := by
  simp_all

/-! ## `simpa`

`simpa using h` simplifies the goal and the hypothesis `h` with the
same lemmas, then closes the goal with `h`. It is the usual last line
when `h` says the same as the goal, up to `simp`. -/

example (h : P ∧ True) : True ∧ P := by
  simpa using h

-- Exercise 6) One line.
example (h : True ∧ (P ∨ False)) : P := by
  simpa using h

/-! ## `grind`

`grind` is Lean's general-purpose automation. It runs several
cooperating decision procedures at once: congruence closure, case
splitting, linear arithmetic, and instantiation of registered lemmas.

On propositional logic it is total. Every statement on sheets a to f
falls to a bare `grind`. -/

example : ((P → Q) → P) → P := by
  grind

example : ¬(P ∧ Q) ↔ (¬P ∨ ¬Q) := by
  grind

/-! So why did you spend six sheets doing this by hand?

Because `grind` is a *finishing* tactic, and the goals it finishes are
the ones you already believe. It does not tell you which lemma to
state, how to structure a theory, or why a proof fails. Those are the
things the rest of this course is about, and `grind` is silent on all
of them.

It also tells you nothing about *why* a statement holds. `itauto`
above distinguishes constructive from classical; `grind` proves both
without comment. A tactic that always succeeds teaches nothing.

Use it. But know what you handed over. -/

-- Exercise 7) Prove this with `grind`, then prove it again by hand
-- with the tactics of sheets a to f. Which proof tells you more?
example : (P ∨ Q) ∧ (¬P) → Q := by
  grind

-- Exercise 8) `grind` fails on exactly one statement of sheet L-a.
-- Which, and why? Write the answer as a comment.
-- (No Lean code required.)
