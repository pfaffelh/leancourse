import Mathlib

/-!
# L-g -- Search and automation

*Logic block, week 5. No chapter of its own: the theory is propositions as types (1.4) and the axioms (2.3), both later.*

Everything on sheets a to f can also be done by machine. This sheet
shows how, and where the limits are.

Doing it by hand first was not wasted: when a tactic fails you need
to know what it was trying to do.

## Tactics introduced here

| tactic     | use it when                                                |
|------------|------------------------------------------------------------|
| `exact?`   | some lemma in Mathlib closes the goal                      |
| `apply?`   | some lemma reduces the goal                                |
| `tauto`    | the goal is a tautology of propositional logic             |
| `itauto`   | the same, but *constructively*                             |
| `simp`     | rewrite with the simp set until nothing changes            |
| `simp_all` | the same, on the goal and all hypotheses at once           |
| `grind`    | the goal is "obvious" and mixes several kinds of reasoning |
-/

variable (P Q R S T : Prop)

/-! ## `exact?` and `apply?`

`exact?` searches Mathlib for a lemma that closes the goal. It prints
what it found. Replace the call by the result -- a search left in a
file makes it slow to compile.

Uncomment and run it: -/

example : ¬¬P ↔ P := by
  -- exact?
  exact not_not

/-! `apply?` is the same for lemmas that leave goals behind.

Both are slow. They are for when you suspect the statement is already
in the library, not for every goal. -/

-- Exercise 1) Use `exact?`, then paste the result.
example : (P ∧ Q) ↔ (Q ∧ P) := by
  sorry

-- Exercise 2) Same. The name you get is worth remembering.
example : (P → Q) ↔ (¬Q → ¬P) := by
  sorry

/-! ## `tauto`

`tauto` proves any tautology of propositional logic. Most of sheets
a to f fall to it. -/

example : ((P → Q) → P) → P := by
  tauto

-- Exercise 3) One line each.
example : ¬(P ∧ Q) ↔ (¬P ∨ ¬Q) := by
  sorry

-- Exercise 4)
example : P ∨ (Q ∧ R) ↔ (P ∨ Q) ∧ (P ∨ R) := by
  sorry

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

-- Exercise 5) For each of the next four, try `itauto` first. Where it
-- fails, use `tauto` and add a comment saying which classical step is
-- needed.

-- Exercise 5a)
example : P → ¬¬P := by
  sorry

-- Exercise 5b)
example : ¬¬P → P := by
  sorry

-- Exercise 5c)
example : (P → Q) → (¬Q → ¬P) := by
  sorry

-- Exercise 5d)
example : (¬Q → ¬P) → (P → Q) := by
  sorry

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

-- Exercise 6) `simp`, then the same with `simp only` and named
-- lemmas. Use `simp?` to find out which it used.
example : (P ∨ False) ↔ P := by
  sorry

/-! ## `simp_all`

`simp` works on the goal. `simp_all` works on the goal *and* every
hypothesis, and repeats until nothing changes, feeding simplified
hypotheses back in. -/

example (h1 : P ∧ True) (h2 : P → Q) : Q ∧ True := by
  simp_all

-- Exercise 7) `simp` alone does not close this; `simp_all` does.
example (h1 : P ∨ False) (h2 : ¬Q → ¬P) : Q ∨ False := by
  sorry

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

-- Exercise 8) Prove this with `grind`, then prove it again by hand
-- with the tactics of sheets a to f. Which proof tells you more?
example : (P ∨ Q) ∧ (¬P) → Q := by
  sorry

-- Exercise 9) `grind` fails on exactly one statement of sheet L-a.
-- Which, and why? Write the answer as a comment.
-- (No Lean code required.)

/-! ## Searching outside Lean

Two services find lemmas by shape or by words. They work from
inside the file:

* `#loogle` -- search by the shape of the statement,
* `#leansearch` -- search in English.

Try `exact?` first. It is offline and exact. Use the services when
you do not know what the lemma is called or whether it exists.

Lean's own documentation and the Zulip chat are the next step. -/

-- Exercise 10) Find the Mathlib name of this law, by any means.
example : ((P ∨ Q) ∨ R) ↔ (P ∨ (Q ∨ R)) := by
  sorry

-- Exercise 11) And of this one.
example : (P → (Q → R)) ↔ ((P ∧ Q) → R) := by
  sorry
