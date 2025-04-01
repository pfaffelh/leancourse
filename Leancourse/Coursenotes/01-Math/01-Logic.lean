import VersoManual
import Manual.Meta

open Verso.Genre Manual

set_option pp.rawOnError true

#doc (Manual) "First steps using Logic" =>
%%%
htmlSplit := .never
tag := "logic"
%%%

# First steps using logic
%%%
tag := "first-steps"
%%%

We start with simple logical statements. We always distinguish (as in every mathematical theorem) between the _hypotheses_ and the _statement_ (or _assertion_, which we also call _goal_ or _target_). To introduce our hypotheses, we write



```lean
variable (P Q R S T : Prop)
```




* Exercises 01-b:

  If you want to prove `⊢ Q` and know that `hPQ : P → Q` is valid, then it is sufficient to prove `⊢ P` (since `hPQ` then implies `⊢ Q`). In this case, `apply hPQ` changes the goal to `⊢ P`.

  Behind an equivalence statement `⊢ P ↔ Q` (type the double arrow as `\iff`) there are actually the two statements `⊢ P → Q` and `⊢ Q → P`. Using `constructor` converts the goal `⊢ P ↔ Q` into two goals for the two directions.

  In Lean, logical negation is noted with `¬` (type `\neg`). The statement `¬P` is defined as `P → false`, where `false` stands for a _false_ statement.
* Sheet 01-c:

  _false_ implies anything. The actual statement is `⊢ false → P`. If the current target is `⊢ P`, and you apply the statement `⊢ false → P` using `apply`, this is equivalent to applying `exfalso`.

  The two expressions `False` and `True` represent two statements that are _false_ and _true_, respectively. So `True` should be easy to prove. This is provided by the tactic `triv`.

  In a proof by contradiction, instead of `⊢ P`, you prove the statement `⊢ ¬P → false` (which, after `intro h`, leads to the assumption `h : ¬P` and the new goal `⊢ false`). This is logically correct, since `P` is true if and only if `¬P` leads to a contradiction, i.e. an false statement. The transformation of the goal in this way is achieved with the tactic `by_contra` or `by_contra h`.
* Exercises 01-e:

  For _and_ and _or_ links between statements, Lean provides the usual notations `∧` (type `\wedge`) and `∨` (type `\vee`). Statements linked with these connections can occur both in a hypothesis and in the goal. Now there are the following four cases:

  * `⊢ P ∧ Q`: Here we must prove the two statements `P` and `Q`. With `constructor` exactly these two goals (with the same assumptions) are created, i.e. `⊢ P` and `⊢ Q`. If these two are shown, then obviously `⊢ P ∧ Q` is also shown.
  * `⊢ P ∨ Q`: To show this, it is sufficient to either show `P` or to show `Q`. In the first case, the target is replaced by `⊢ P` with `left`, and by `⊢ Q` with `right`.
  * `h : P ∧ Q`: Apparently, the hypothesis `h` breaks down into two hypotheses, both of which must hold. Using `cases' h with hP hQ`, `h : P ∧ Q` is transformed into two hypotheses, namely `hP : P` and `hQ : Q`.
  * `h : P ∨ Q`: Similar to the last case, `cases' h with hP hQ` now generates two new goals, one where `h : P ∨ Q` has been replaced by `hP : P`, and one where `h : P ∨ Q` has been replaced by `hQ : Q`. This is logically correct, because this way you can distinguish the cases where `P` or `Q` apply.
* Exercises 01-e:

  This is about introducing new hypotheses. With the `by_cases` tactic - applied to a hypothesis `h : P` - all possibilities are gone through that `P` can assume. These are that `P` is either `true` or `false`. So `by_cases h : P` introduces two new goals, one with the hypothesis `h : P` and one with the hypothesis `h : ¬P`.

  A very general tactic is `have`. Any hypotheses can be formulated here that must first be shown.

* Exercise 01-f:

  Now we come to abbreviations. First, we introduce the abbreviation `⟨ hP, hQ, hR ⟩` (type `\langle` and `\rangle`) for the `∧` conjunction of the statements `hP` `hQ` and `hR`. (This works with two or more than three hypotheses). Similarly, `(hP | hQ)` is a shorthand for `hP ∨ hQ`. These two shorthands can also be nested. The three tactics we discuss here are `rintro` for `intros` + `cases`, `rcases` for a more flexible version of `cases` that allows the notations just introduced, and `obtain` for `intro` + `have`.

* Exercise 01-g: Quantifiers

  Quantifiers such as `∀` (type `\forall`) and `∃` (type `\exists`) have been known since the first semester. These can also occur in `Lean`. We distinguish whether these quantifiers occur in the goal or in a hypothesis. The following is a small table of which tactics are appropriate in each case. Exact explanations are in `01-g.lean`.

:::table (align := left) (header := true)
* + Quantifier
  + in goal
  + in hypothesis `h`
* + `∀ (x : X), _`
  + `intro x`
  + `apply h _`
* + `∃ (x : X), _`
  + `use _`
  + `cases h`
:::

* Exercises 01-h:

  Slowly but surely, we are working our way towards applications with _real_ mathematics, but a few things are still missing. In this sheet, we learn to prove equalities using _refl_. For later work with `=` or `↔` (type `\iff`) statements, `rw` is very important because here you can rewrite things, i.e. you can use propositional equalities. Since there are already a lot of statements in `Mathlib`, it is good to have a kind of search function. This is provided by `apply?`. We also learn how to define functions. This is done using the `fun` keyword. For example, `fun x ↦ 2*x` (type `\mapsto`, but `=>` works as well) represents the function `x ↦ 2x`. If you have `let f : X → X := fun x ↦ 2*x`, then `f 1` returns the function value for `x = 1`.
