import Mathlib -- load everything, in particular tactics

/-!
# (witness) L-a -- Propositions and implication

*Logic block, week 1. No chapter of its own: the theory is propositions as types (1.4) and the axioms (2.2), both later.*

Everything on this sheet is about *propositions*: statements that are
either true or false. We never talk about numbers, sets or functions
here, only about `P`, `Q`, `R`, ... and how they combine. The only
connective on this sheet is the implication `→`.

## Tactics introduced here

| tactic       | use it when                                          |
|--------------|------------------------------------------------------|
| `trivial`    | the goal is `True`                                   |
| `intro hP`   | the goal is `P → Q`: assume `P`, then prove `Q`      |
| `exact hP`   | `hP` is literally a proof of the goal                |
| `assumption` | *some* hypothesis is a proof of the goal             |
| `apply hPQ`  | `hPQ : P → Q` and the goal is `Q`: now prove `P`     |
| `revert hP`  | the opposite of `intro`: put `hP` back into the goal |

Work through the sheet from top to bottom. Each tactic is explained
and demonstrated before the first exercise that needs it.
-/

variable (P Q R S T : Prop)

/-! ## Statements, proofs, and `by`

Lean has three ways to state something:

* `example : ...` -- no name, used for one-off statements,
* `lemma name : ...` and `theorem name : ...` -- the same thing, but
  named, so that you can refer to them later.

So `example` is always followed directly by `:`, while the other two
take a name first.

Whatever comes after `:=` is the *proof*. There are two styles: a
*term proof*, which writes the proof down directly, and a *tactic
proof*, which starts with the keyword `by` and then builds the proof
step by step. We will work in tactic mode almost exclusively, because
it shows you the goal as you go.

The simplest proposition is `True`. It holds by definition, and the
tactic `trivial` is exactly the tactic that says so.
-/

example : True := by
  trivial

/-! ## `sorry`

Every exercise below starts with `sorry`. This tactic closes *any*
goal without proving anything, which is how an unfinished file still
compiles. Lean warns you about each one
(`declaration uses 'sorry'`).

`sorry` really does close any goal, including plainly false ones:

```
example : False := by
  sorry
```

Try that in a scratch file and watch the warning appear. We do not
put it here, so that "no `sorry` left in this file" stays a
meaningful statement about your work.

**Your task on every sheet: make it `sorry`-free.**
-/

/-! ## `intro`, `exact`, `assumption`

An implication `P → Q` says: *if* `P` holds, *then* `Q` holds. To
prove a goal `⊢ P → Q` you therefore assume `P` and prove `Q`. The
tactic for that is `intro`:

`intro hP` turns the goal `⊢ P → Q` into a hypothesis `hP : P`
together with the new goal `⊢ Q`.

Once the goal is identical to a hypothesis you are done. There are
two tactics for that: `exact hP` names the hypothesis you mean, and
`assumption` searches all hypotheses for one that fits.
-/

example : P → P := by
  intro hP
  exact hP

example : P → P := by
  intro hP
  assumption

/-! Several `intro`s can be written in one go: `intro h1 h2 h3`.

Note that Lean writes implication with a single arrow `→`, not the
double arrow `=>` you may know from other languages. Hover over the
symbol in VS Code to see how to type it (`\to`, or `\r`).

Note also that we do not have to repeat `P : Prop` in every statement:
the `variable` line above declared `P`, `Q`, `R`, `S`, `T` once and
for all.

*Side note.* The arrow `→` is also the arrow of function types, and
that is no accident: a proof of `P → Q` really is a function turning
proofs of `P` into proofs of `Q`. This is the
[Curry-Howard correspondence](https://en.wikipedia.org/wiki/Curry%E2%80%93Howard_correspondence),
and it means the proof above can also be given as a term: -/

example : P → P := by
  exact fun hP ↦ hP

-- Exercise 1) Assume `P`, then assume it again.
example : P → (P → P) := by
  intro hP _
  exact hP

-- Exercise 2) Here the hypothesis stands before the colon, so it is
-- available from the start; no `intro` is needed for it.
example (hQ : Q) : P → Q := by
  intro _
  exact hQ

-- Exercise 3) Two `intro`s. Remember that a hypothesis `hPQ : P → Q`
-- can be *applied* to a proof of `P`, written `hPQ hP`, exactly like
-- a function.
example : P → (P → Q) → Q := by
  intro hP hPQ
  exact hPQ hP

/-! ## `apply`

Suppose the goal is `⊢ Q` and you have `hPQ : P → Q`. Then it is
enough to prove `P`. The tactic `apply hPQ` performs exactly this
step: it replaces the goal `Q` by the goal `P`.

Compare the two tactics:

* `exact h` needs `h` to be a proof of the goal *already*;
* `apply h` needs `h` to *end* in the goal, and leaves you with its
  premises as new goals.
-/

example (hP : P) (hPQ : P → Q) : Q := by
  apply hPQ
  exact hP

/-! The same proof in the function-application style: -/

example (hP : P) (hPQ : P → Q) : Q := by
  exact hPQ hP

/-! Since any proof of the goal trivially "ends in" the goal, `apply`
can also be used where `exact` would do: -/

example (hP : P) : P := by
  apply hP

-- Exercise 4) Chain two implications. You can do this with `apply`
-- twice, or in one line in the function style.
example (hP : P) (hPQ : P → Q) (hQR : Q → R) : R := by
  exact hQR (hPQ hP)

-- Exercise 5) Transitivity, this time as a statement in its own right.
example : (P → Q) → (Q → R) → (P → R) := by
  intro hPQ hQR hP
  exact hQR (hPQ hP)

-- Exercise 6) A small puzzle. Not all the hypotheses are needed --
-- find a path from `T` to `R`.
example (hPQ : P → Q) (hQT : Q → T) (hQR : Q → R) (hRS : R → S)
    (hTP : T → P) (hRT : R → T) : T → R := by
  intro hT
  exact hQR (hPQ (hTP hT))

/-! ## `revert`

`revert` is the exact opposite of `intro`: it takes a hypothesis out
of the context and puts it back into the goal.

If the context contains `hP : P` and the goal is `⊢ Q`, then
`revert hP` removes `hP` and makes the goal `⊢ P → Q`.
-/

example (hPQ : P → Q) (hP : P) : Q := by
  revert hP
  -- the goal is now `⊢ P → Q`
  exact hPQ

/-! You will not need `revert` often, but it is worth knowing for two
reasons. It makes a symmetry visible -- a premise on the left of `→`
and a hypothesis in the context are the same thing seen from two
sides -- and it is occasionally the only way to put a goal into the
shape that some other tactic wants. -/

-- Exercise 7) Finish this one *without* applying `h` to `hP`. The
-- `revert` is already there -- look at what the goal becomes.
example (h : P → Q) (hP : P) : Q := by
  revert hP
  exact h

/-! ## Which statements actually hold?

Not everything you can write down is true. Proving a statement is
only half the skill; the other half is seeing that a statement is
*not* provable, and why.

Exactly one of the next three cannot be proved. Prove the other two.
For the remaining one, leave its `sorry` in place and replace the
comment line above it by a sentence saying why no proof can exist.
-/

-- Exercise 8a)
example : P → Q → P := by
  intro hP _
  exact hP

-- CHECK: expect 1 sorry -- 8b is deliberately not provable.
-- Exercise 8b) NOT PROVABLE: from two proofs of `P` nothing can be
-- said about the unrelated proposition `Q`.
example : P → P → Q := by
  sorry

-- Exercise 8c)
example : P → Q → Q := by
  intro _ hQ
  exact hQ

/-! ## Implications with several premises

A statement such as `P → Q → R` carries no brackets, and Lean reads
it as `P → (Q → R)`: given a proof of `P`, what you get back is
itself an implication, still waiting for a proof of `Q`.

That is why `intro hP hQ` works on such a goal, and why a hypothesis
`h : P → Q → R` is applied in two steps, as `h hP hQ`. -/

example (h : P → Q → R) (hP : P) (hQ : Q) : R := by
  exact h hP hQ

-- Exercise 9) Supply the premises in the other order.
example (h : P → Q → R) (hQ : Q) : P → R := by
  intro hP
  exact h hP hQ

-- Exercise 10) Worth staring at: both hypotheses need `P`, so you
-- will have to use the proof of `P` twice.
example (h : P → Q → R) (hPQ : P → Q) : P → R := by
  intro hP
  exact h hP (hPQ hP)

-- Exercise 11) A harder one to finish on. Nothing new is needed --
-- only `intro`, `apply` and `exact`, in the right order.
example : (P → Q → R) → (P → Q) → (P → R) := by
  intro h hPQ hP
  exact h hP (hPQ hP)
