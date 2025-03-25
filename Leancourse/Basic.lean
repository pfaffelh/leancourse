import Lean
import VersoManual
import DemoTextbook
import UsersGuide.Markup
import Leancourse.Meta.Table

open Verso.Genre Manual
open DemoTextbook.Exts

set_option pp.rawOnError true

def Inline.br : Manual.Inline where
  name := `My.Namespace.br

def My.Namespace.br (_ : Array (Verso.Doc.Inline Manual)) : Verso.Doc.Inline Manual :=
  .other Inline.br #[]

open Verso.Output.Html in
@[inline_extension My.Namespace.br]
def My.Namespace.br.descr : InlineDescr where
  traverse _ _ _ := pure none
  toHtml := some fun _ _ _ _ =>
    pure {{<br/>}}
  toTeX := none

open My.Namespace

example : 2 + 2 = 4 :=
  by rfl


#doc (Manual) "Interactive Theorem Proving using Lean, Summer 2025" =>

%%%
authors := ["Peter Pfaffelhuber"]
%%%

These are the notes for a course on formal proving with the interactive theorem prover Lean4 (in the following we just write Lean) in the summer semester of 2025 at the University of Freiburg. To be able to work through the course in a meaningful way, the following technical preparations are to be made:

* Installation of [vscode](https://code.visualstudio.com/).
* Local installation of Lean and the associated tools: Please follow these [instructions](https://github.com/leanprover-community/mathlib4/wiki/Using-mathlib4-as-a-dependency).
* Installing the course repository: Navigate to a location where you would like to put the course materials and use `git clone get https://github.com/pfaffelh/leancourse`.
* After `cd leancourse` and `code .`, you should see some code which looks a bit like mathematics. On the left hand side of the `vscode` window, you can click and install an extension for `Lean`.
* The directory `Exercises` contains the material for the course. We recommend that you first copy this directory, for example to `myExercises`. Otherwise, an update of the repository may overwrite the local files.
* To update the course materials, enter `git pull` from within the `leancourse`directory.

# Introduction

The course is designed for mathematics students and has at least two goals:

* Learning the techniques for interactive formal Theorem proofing using Lean: In recent years, efforts to prove mathematical theorems with the help of computers have increased dramatically. While a few decades ago, it was more a matter of consistently processing many cases that were left to the computer, interactive theorem provers are different. Here, a very small core can be used to understand or interactively generate all the logical conclusions of a mathematical proof. The computer then reports interactively on the progress of the proof and when all the steps have been completed.
* Establishing connections to some mathematical material: On the one hand, the mathematical details needed in this course should not be the main issue of this course. On the other hand, in order to _explain_ how a proof (or calculation or other argument) to a computer, you first have to understand it very well yourself. Furthermore, you have to plan the proof well - at least if it exceeds a few lines - so that the commands you enter (which we will call tactics) fit together.

# First steps using logic

We start with simple logical statements. We always distinguish (as in every mathematical theorem) between the _hypotheses_ and the _statement_ (or _assertion_, which we also call _goal_ or _target_). To introduce our hypotheses, we write `variable (P Q R S T : Prop)`. Note that the lean syntax does not use the usual double arrow `=>` here, but a single `→`. We are going through the following logical inferences here:
* Exercises 01-a:
  The statement `⊢ P → Q` (i.e. `P` implies `Q`) means that `Q` is valid if one may assume that the hypothesis `P` is correct. This transition from `⊢ P → Q` to the hypothesis `hP : P` with target `⊢ Q` is done using `intro hP`. Several `intro` commands can be abbreviated using `intro h1 h2...`.

  If the hypothesis `hP : P` holds and we want to prove `⊢ P`, then we just have to apply `hP` to the goal. If goal and hypothesis are identical, this is done with `exact hP`. In a more general way, `assumption` searches all hypotheses for those that are identical with the goal by definition.
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


```lean
variable (P Q R S T : Prop)
```

```lean
example : P → Q := by
  intro h
  sorry
```

```lean
example (hP : P) : (P → Q) → Q := by
  intro hPQ
  exact hPQ hP
```


```
Proof state   Command         New proof state

⊢ P → Q       intro hP        hP : P
                              ⊢ Q
```

Assume we have `⊢ Q`, then all makes sense!

{docstring Lean.Parser.Tactic.apply}

Documentation can take many forms:

 * References
 * Tutorials
 * Etc

```lean
example : 2 + 2 = 4 :=
  by rfl
```

:::table (header := true) (align := left)
* + proof state
  + tactic
  + new proof state
* + `⊢ P → Q`
  + `intro hP`
  + `P`{br}[]`⊢ Q`
:::

:::table (header := true)
* + goal
  + tactic
  + new goal
* + `Prod`
  + `Type u`
  + `Type v`
:::

:::table (header := true)
* + Type
  + First Projection
  + Second Projection
  + Dependent?
  + Universe
* + `Prod`
  + `Type u`
  + `Type v`
  + ❌️
  + `Type (max u v)`
:::




:::table (header := true) (align := left)
* + Proof state
  + Tactic
  + New proof state
* + `⊢ P → Q`
  + `intro hP`
  + `hP : P` {br}[] `⊢ Q`
* + `⊢ P → Q → R`
  + `intro hP hQ`
  + `hP : P` {br}[] `hQ : Q` {br}[] `⊢ R`
* + `p : α → Prop` {br}[] `⊢ ∀ (x : α), f x`
  + `intro x`
  + `f: α → Prop` {br}[] `x : α` {br}[] `⊢ p x`
* + `h : P` {br}[] `⊢ P`
  + `exact h`
  + `no goals 🎉`
* + `h : P` {br}[] `⊢ P`
  + `assumption`
  + `no goals 🎉`
* + `h : P → Q` {br}[] `⊢ P`
  + `apply h`
  + `⊢ Q`
* + `h₁ : P → Q` {br}[] `h₂ : Q → R`  {br}[] `⊢ R`
  + `apply h₂ h₁`
  + `h₁ : P → Q` {br}[] `h₂ : Q → R`  {br}[] `⊢ P`
* + ⊢ `P ∧ Q → P`
  + `tauto` or `tauto!`
  + `no goals 🎉`
* + `⊢ true`
  + `triv`
  + `no goals 🎉`
* + `h : P` {br}[] `⊢ Q`
  + `exfalso`
  + `h : P` {br}[] `⊢ false`
* + `⊢ P`
  + `by_contra h`
  + `h : ¬P` {br}[] `⊢ false`
* + `⊢ P`
  + `by_cases h : Q`
  + `h : Q` {br}[] `⊢ P` {br}[] `h : ¬Q` {br}[] `⊢ P`
* + `h : P ∧ Q` {br}[] `⊢ R`
  + `cases' h with hP hQ`
  + `hP : P` {br}[] `hQ : Q` {br}[] `⊢ R`
* + `h : P ∧ Q` {br}[] `⊢ R`
  + `obtain ⟨hP, hQ⟩ := h`
  + `hP : P` {br}[] `hQ : Q` {br}[] `⊢ R`
* + `h : P ∨ Q` {br}[] `⊢ R`
  + `cases' h with hP hQ`
  +  `hP : P` {br}[] `⊢ R` {br}[] `hQ : Q ⊢ R`
* + `h : false` {br}[] `⊢ P`
  + `cases h`
  + `no goals 🎉`
* + `⊢ P → false`
  + `change ¬P`
  + `⊢ ¬P`
* + `⊢ P ∧ Q`
  + `constructor`
  + `⊢ P` {br}[] `⊢ Q`
* + `⊢ P ↔ Q`
  + `constructor`
  + `⊢ P → Q` {br}[] `⊢ Q → P`
* + `⊢ P ↔ P` or {br}[] `⊢ P = P`
  + `rfl`
  + `no goals 🎉`
* + `h : P ↔ Q` {br}[] `⊢ P`
  + `rw [h]`
  + `h : P ↔ Q` {br}[] `⊢ Q`
* + `h : P ↔ Q` {br}[] `hP : P`
  + `rw [h] at hP`
  + `h : P ↔ Q` {br}[] `hP : Q`
* + `h : P ↔ Q` {br}[] `⊢ Q`
  + `rw [← h]`
  + `h : P ↔ Q` {br}[] `⊢ P`
* + `h : P ↔ Q` {br}[] `hQ : Q`
  + `rw [← h] at hQ`
  + `h : P ↔ Q` {br}[] `hQ : P`
* + `⊢ P ∨ Q`
  + `left`
  + `⊢ P`
* + `⊢ P ∨ Q`
  + `right`
  + `⊢ Q`
* + `⊢ 2 + 2 < 5`
  + `norm_num`
  + `no goals 🎉`
* + `p : α → Prop` {br}[] `y : α` {br}[] `⊢ ∃ (x : α), p x`
  + `use y`
  + `p : α → Prop` {br}[] `y : α` {br}[]  `⊢ f y`
* + `x y : ℝ` {br}[] `⊢ x + y = y + x`
  + `ring`
  + `no goals 🎉`
* + `p : α → Prop` {br}[] `⊢ ∀ (x : α), p x`
  + `intro x`
  + `p : α → Prop` {br}[] `x : α` {br}[] `p x`
* + `h₁ : a < b` {br}[] `h₂ : b ≤ c` {br}[] `⊢ a < c`
  + `linarith`
  + `no goals 🎉`
* + `h : P` {br}[] `⊢ Q`
  + `clear h`
  + `⊢ Q`
* + `p : ℕ → Prop` {br}[] `h : ∀ (n : ℕ), p n` {br}[] `⊢ P`
  + `specialize h 13`
  + `p : ℕ → Prop` {br}[] `h : p 13` {br}[]  `⊢ P`
* + `p : ℕ → ℕ → Prop` {br}[] `h : ∀ (n : ℕ), ∃ (m : ℕ), p n m`
  + `obtain ⟨m, hm⟩ := h 27`
  + `p : ℕ → ℕ → Prop` {br}[] `h : ∀ (n : ℕ), ∃ (m : ℕ), p n m` {br}[] `m : ℕ` {br}[] `hm : f 27 m`
* + `⊢ R`
  + `have h : P ↔ Q`
  + `⊢ P ↔ Q` {br}[] `h : P ↔ Q` {br}[] `⊢ R`
* + `h₁ : a < b` {br}[] `h₂ : b < c` {br}[] `⊢ a < c`
  + `apply?`
  + `no goals 🎉` {br}[] Try this: {br}[] `exact lt_trans h₁ h₂`
* + `hQ : Q` {br}[] `⊢ P ∧ Q`
  + `refine ⟨ _, hQ ⟩`
  + `hQ : Q` {br}[] `⊢ P`
* + `⊢ P ∨ Q → R`
  + `rintro (hP | hQ)` {br}[] = {br}[] `intro h` {br}[] `cases' h with hP hQ`
  + `hP : P` {br}[] `⊢ R` {br}[] `hQ : Q` {br}[] `⊢ R`
* + `⊢ P ∧ Q → R`
  + `rintro ⟨hP , hQ⟩` {br}[] = {br}[] `intro h` {br}[]
`cases' h with h1 h2`
  + `hP : P` {br}[] `hQ : Q` {br}[] `⊢ R`
* + `h : P ∧ Q ∨ P ∧ R` {br}[] `⊢ S`
  + `rcases h with (⟨hP1,hQ⟩|⟨hP2,hR⟩)`
  + `hP1 : P` {br}[] `hQ : Q` {br}[] `⊢ S` {br}[] `hP2 : P` {br}[] `hR : R`{br}[] `⊢ S`
* + `m n : ℕ` {br}[] `⊢ n + 0 = m`
  + `simp`
  + `m n : ℕ` {br}[] `n = m`
* + `h : n + 0 = m` {br}[] `⊢ P`
  + `simp at h`
  + `h : n = m` {br}[] `⊢ P`
:::




# Genres
%%%
tag := "genres"
%%%


:::paragraph
Documentation comes in many forms, and no one system is suitable for representing all of them.
The needs of software documentation writers are not the same as the needs of textbook authors, researchers writing papers, bloggers, or poets.
Thus, Lean's documentation system supports multiple _genres_, each of which consists of:

 * A global view of a document's structure, whether it be a document with subsections, a collection of interrelated documents such as a web site, or a single file of text
 * A representation of cross-cutting state such as cross-references to figures, index entries, and named theorems
 * Additions to the structure of the document - for instance, the blog genre supports the inclusion of raw HTML, and the manual genre supports grouping multiple top-level blocks into a single logical paragraph
 * Procedures for resolving cross references and rendering the document to one or more output formats

All genres use the same markup syntax, and they can share extensions to the markup language that don't rely on incompatible document structure additions.
Mixing incompatible features results in an ordinary Lean type error.
:::

# Docstrings
%%%
tag := "docstrings"
%%%

Docstrings can be included using the `docstring` directive. For instance,

```
{docstring List.forM}
```

# Tactics

## Cheatsheet

:::table (align := left) (header := true)
* + Proof state
  + Tactic
  + New proof state
* + `⊢ P → Q`
  + `intro hP`
  + `hP : P` {br}[] `⊢ Q`
* + `⊢ P → Q → R`
  + `intro hP hQ`
  + `hP : P` {br}[] `hQ : Q` {br}[] `⊢ R`
* + `p : α → Prop` {br}[] `⊢ ∀ (x : α), f x`
  + `intro x`
  + `f: α → Prop` {br}[] `x : α` {br}[] `⊢ p x`
* + `h : P` {br}[] `⊢ P`
  + `exact h`
  + `no goals 🎉`
* + `h : P` {br}[] `⊢ P`
  + `assumption`
  + `no goals 🎉`
* + `h : P → Q` {br}[] `⊢ P`
  + `apply h`
  + `⊢ Q`
* + `h₁ : P → Q` {br}[] `h₂ : Q → R` {br}[] `⊢ R`
  + `apply h₂ h₁`
  + `h₁ : P → Q` {br}[] `h₂ : Q → R` {br}[] `⊢ P`
* + `⊢ P ∧ Q → P`
  + `tauto` oder `tauto!`
  + `no goals 🎉`
* + `⊢ true`
  + `triv`
  + `no goals 🎉`
* + `h : P` {br}[] `⊢ Q`
  + `exfalso`
  + `h : P` {br}[] `⊢ false`
* + `⊢ P`
  + `by_contra h`
  + `h : ¬P` {br}[] `⊢ false`
* + `⊢ P`
  + `by_cases h : Q`
  + `h : Q` {br}[] `⊢ P` {br}[] `h : ¬Q` {br}[] `⊢ P`
* + `h : P ∧ Q` {br}[] `⊢ R`
  + `cases' h with hP hQ`
  + `hP : P` {br}[] `hQ : Q` {br}[] `⊢ R`
* + `h : P ∧ Q` {br}[] `⊢ R`
  + `obtain ⟨hP, hQ⟩ := h`
  + `hP : P` {br}[] `hQ : Q` {br}[] `⊢ R`
* + `h : P ∨ Q` {br}[] `⊢ R`
  + `cases' h with hP hQ`
  +  `hP : P` {br}[] `⊢ R` {br}[] `hQ : Q ⊢ R`
* + `h : false` {br}[] `⊢ P`
  + `cases h`
  + `no goals 🎉`
* + `⊢ : P → false`
  + `change ¬P`
  + `⊢ ¬P`
* + `⊢ P ∧ Q`
  + `constructor`
  + `⊢ P` {br}[] `⊢ Q`
* + `⊢ P ↔ Q`
  + `constructor`
  + `⊢ P → Q` {br}[] `⊢ Q → P`
* + `⊢ P ↔ P` oder {br}[] `⊢ P = P`
  + `rfl`
  + `no goals 🎉`
* + `h : P ↔ Q` {br}[] `⊢ P`
  + `rw h`
  + `h : P ↔ Q` {br}[] `⊢ Q`
* + `h : P ↔ Q` {br}[] `hP : P`
  + `rw h at hP`
  + `h : P ↔ Q` {br}[] `hP : Q`
* + `h : P ↔ Q` {br}[] `⊢ Q`
  + `rw ← h`
  + `h : P ↔ Q` {br}[] `⊢ P`
* + `h : P ↔ Q` {br}[] `hQ : Q`
  + `rw ← h at hQ`
  + `h : P ↔ Q` {br}[] `hQ : P`
* + `⊢ P ∨ Q`
  + `left`
  + `⊢ P`
* + `⊢ P ∨ Q`
  + `right`
  + `⊢ Q`
* + `⊢ 2 + 2 < 5`
  + `norm_num`
  + `no goals 🎉`
* + `p : α → Prop` {br}[] `y : α` {br}[] `⊢ ∃ (x : α), f x`
  + `use y`
  + `p : α → Prop` {br}[] `y : α` {br}[]  `⊢ f y`
* + `x y : ℝ` {br}[] `⊢ x + y = y + x`
  + `ring`
  + `no goals 🎉`
* + `p : α → Prop` {br}[] `⊢ ∀ (x : α), p x`
  + `intro x`
  + `p : α → Prop` {br}[] `x : α` {br}[] `p x`
* + `h₁ : a < b` {br}[] `h₂ : b ≤ c` {br}[] `⊢ a < c`
  + `linarith`
  + `no goals 🎉`
* + `h : P` {br}[] `⊢ Q`
  + `clear h`
  + `⊢ Q`
* + `p : ℕ → Prop` {br}[] `h : ∀ (n : ℕ), p n` {br}[]  `⊢ P`
  + `specialize h 13`
  + `p : ℕ → Prop` {br}[] `h : p 13` {br}[] `⊢ P`
* + `p : ℕ → ℕ → Prop` {br}[] `h : ∀ (n : ℕ), ∃ (m : ℕ), f n m`
  + `obtain ⟨m, hm⟩ := h 27`
  + `f : ℕ → ℕ → Prop` {br}[] `h : ∀ (n : ℕ), ∃ (m : ℕ), f n m` {br}[] `m : ℕ` {br}[] `hm : f 27 m`
* + `⊢ R`
  + `have h : P ↔ Q`
  + `⊢ P ↔ Q` {br}[] `h : P ↔ Q` {br}[] `⊢ R`
* + `h₁ : a < b` {br}[] `h₂ : b < c` {br}[] `⊢ a < c`
  + `apply?`
  + `no goals 🎉` {br}[] Try this: {br}[]  `exact lt_trans h₁ h₂`
* + `hQ : Q` {br}[] `⊢ P ∧ Q`
  + `refine ⟨ _, hQ ⟩`
  + `hQ : Q` {br}[] `⊢ P`
* + `⊢ P ∨ Q → R`
  + `rintro (hP | hQ)` {br}[] = {br}[] `intro h` {br}[] `cases h with hP hQ`
  + `hP : P` {br}[] `⊢ R` {br}[] `hQ : Q` {br}[] `⊢ R`
* + `⊢ P ∧ Q → R`
  + `rintro ⟨hP , hQ⟩` {br}[] = {br}[] `intro h` {br}[] `cases h with h1 h2`
  + `hP : P` {br}[] `hQ : Q` {br}[] `⊢ R`
* + `h : P ∧ Q ∨ P ∧ R` {br}[] `⊢ S`
  + `rcases h with (⟨hP1,hQ⟩|⟨hP2,hR⟩)`
  + `hP1 : P` {br}[] `hQ : Q` {br}[] `⊢ S` {br}[] `hP2 : P` {br}[] `hR : R` {br}[] `⊢ S`
* + `⊢ n + 0 = n`
  + `simp`
  + `no goals 🎉`
* + `h : n + 0 = m` {br}[] `⊢ P`
  + `simp at h`
  + `h : n = m` {br}[] `⊢ P`
:::


## Summary of several tactics

### `apply`

**Summary:** If we have the goal `⊢ Q`, and a proof of `h : P → Q`, we only need to find a proof for `P`. This transition happens by `apply h`.

:::table (align := left) (header := true)
* + , h : P → Q {br}[] ⊢ P
  + apply h
  + ⊢Q
* + h₁ : P → Q {br}[] h₂ : Q → R  {br}[] ⊢ R
  + apply h₂ h₁
  + h₁ : P → Q {br}[] h₂ : Q → R  {br}[] ⊢ P
:::

The `apply`-tactics works iteratively. This means that if `apply h` makes no progress, it uses the placeholder `_` and tries to make `apply h _`.

```lean
example (hP : P) (hQ : Q) (hPQR : P → Q → R) : R := by
  apply hPQR
  · exact hP
  · exact hQ
```


**Remarks:**
* `apply` works up to equality by definition. This can be seen in the example above, where `¬P ↔ (P → False)` is true by definition.
* `apply h` is frequently identical to `refine ?_`.
* If the use of `apply` closes the current goal, you might as well use `exact` instead of `apply`.

### `assumption`

**Summary**: If the current goal is identical to a hypothesis, `assumption` closes the goal.


**Remarks:**
* Like other tactics, `assumtion` works up to equality by definition.
* Here is a trick, which works well with `assumption`. If you write `<;>` after a tactic, the following command is applied to all goals.

```lean
example (hP : P) (hQ : Q) : P ∧ Q := by
  constructor <;> assumption
```
