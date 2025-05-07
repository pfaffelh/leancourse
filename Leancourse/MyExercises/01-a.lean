import Mathlib -- load everything, in particular tactics

/- We start by studying `Prop`-types. These are like mathematical theorems, i.e. can be either true or false. We start by introducing a bunch of variables which are generic propositions. -/

variable (P Q R S T: Prop)

/-- Apart from these types, we will in this and the upcoming exercises mostly deal with implications, i.e. Types of the form `P → Q`.-/

/- Let's start simple. -/

example : True := by
  trivial

/-- Some remark:
* In Lean, we have `example` (which does not need an own name), `lemma` and `theorem` (both of which have a name). So, `example` is always followed by `:` while we have `lemma <nameOfLemma> : ` and `theorem <nameOfTheorem> :` for the latter two.
* The proof of the `True`-statement is right of `:=`. In principle, there are two types of proofs: term-proofs, and tactic proofs. We will only deal with tactic proofs, which always start with the `by` keyword.
* Here, `triv` is a tactic, and has the only task of showing `True`. -/

/-
With _intro_ you transform an assertion left of the first → intro a hypothesis and the remaining assertion is the new goal. If the goal is identical to a hypothesis, _assumption_ closes the goal. Alternatively, you can use _exact_.
 -/

example : P → P := by
  intro hP
  assumption

example : P → P := by
  intro hP
  exact hP

/- Note that the lean syntax does not use the usual double arrow `=>` here, but a single `→`. (Hover over the symbol in vscode in order to learn how to type it.) -/

/- Side note: the `→` looks like a function application, doesn't it? In fact, theoretical computer scientists have shown that there is a close connection between applying functions and proving theorems; see [Curry-Howard correspondance](https://en.wikipedia.org/wiki/Curry%E2%80%93Howard_correspondence). This is why the proof could as well look like this: -/

example : P → P := by
  exact fun x ↦ x

/- Here are some exercises. In all of them, we use the `sorry` axiom/tactics to get started. This tactics closes every goal (no matter if it is true or not). Of course, using `sorry` is like cheating, so your task is to make the exercises `sorry`-free.-/

/- The statement `⊢ P → Q` (i.e. `P` implies `Q`) means that `Q` is valid if one may assume that the hypothesis `P` is correct. This transition from `⊢ P → Q` to the hypothesis `hP : P` with target `⊢ Q` is done using `intro hP`. Several `intro` commands can be abbreviated using `intro h1 h2...`.

If the hypothesis `hP : P` holds and we want to prove `⊢ P`, then we just have to apply `hP` to the goal. If goal and hypothesis are identical, this is done with `exact hP`. In a more general way, `assumption` searches all hypotheses for those that are identical with the goal by definition.-/

/- Note that in all exercises, we do not need to say that `P : Prop` since we have done this once and forever at the start of tis file. -/

-- Exercise 1)
example : P → (P → P) := by
  intro h₁ h₂
  exact h₂

-- Exercise 2)
-- Here the proof starts with a hypothesis, which we do not have _intro_duced earlier.
example (hQ : Q) : (P → Q) := by
  intro _
  exact hQ

-- Exercise 3) Why not try with `intro hP hPQ`. This shortens it a bit. However, note that you can also use something like `hPQ hP`, which applies the hypothesis `P → Q` to `P`.
example : P → (P → Q) → Q := by
  intro h1 h2
  exact h2 h1

-- Exercise 4) Make up your mind which of the following `examples` are valid, and prove them.
example : P → Q → P := by
  intro h1 h2
  exact h1

example : P → P → Q := by
  sorry

example : P → Q → Q := by
  intro h1 h2
  exact h2
