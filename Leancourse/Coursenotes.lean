import Lean
-- import VersoManual
-- import DemoTextbook
-- import UsersGuide.Markup
-- import Leancourse.Meta.Table

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
* Local installation of Lean and the associated tools: Please follow these [instructions](https://leanprover-community.github.io/get_started.html#regular-install).
* Installing the course repository: Navigate to a location where you would like to put the course materials and use
```
git clone https://github.com/pfaffelh/leancourse`
cd leancourse
lake exe cache get
```
When you type `code .` within the `leancourse` folder, you should see some code which looks a bit like mathematics.
* The directory `Leancourse/Exercises` contains the material for the course. We recommend that you first copy this directory, for example to `myExercises`. Otherwise, an update of the repository may overwrite the local files.
* To update the course materials, enter `git pull` from within the `leancourse`directory.


# Introduction

## Goals

The course is designed for mathematics students and has at least two goals:

* Learning the techniques for interactive theorem proofing using Lean: In recent years, efforts to prove mathematical theorems with the help of computers have increased dramatically. While a few decades ago, it was more a matter of consistently processing many cases that were left to the computer, interactive theorem provers are different. Here, a very small core can be used to understand or interactively generate all the logical conclusions of a mathematical proof. The computer then reports interactively on the progress of the proof and when all the steps have been completed.
* Establishing connections to some mathematical material: At least in the first half, the mathematical details needed in this course should not be the main issue of this course. However, in order to _explain_ how a proof (or calculation or other argument) to a computer, you first have to understand it very well yourself. Furthermore, you have to plan the proof well - at least if it exceeds a few lines - so that the commands you enter (which we will call tactics) fit together. The course intends to teach both, first steps in `Lean` and learning a bunch of these tactics, and make a deeper dive into some mathematical material.

## Other material and Theorem provers

Lean is not the only theorem prover, and, of course, this course is not the only course trying to teach Lean to you. Other Theorem provers (which all will be neglected here) are:

* [Rocq](https://rocq-prover.org/) (formerly COQ)
* [Isabelle/HOL ](https://isabelle.in.tum.de/)

Other courses, which you might want to have a look at are:

* [_Natural Number Game_](https://adam.math.hhu.de/#/g/leanprover-community/nng4): In case you are reading this text in advance and have some spare time, it is highly recommended to start this (online) game, making you prove first things on `ℕ` using Lean. It is a classical way to start your first contact with Lean.
* [_Formalizing Mathematics 2025_](https://b-mehta.github.io/formalising-mathematics-notes/) by Bhavik Mehta, based on notes by Kevin Buzzard: these notes have inspired at least the format of the present course.
* [_Mathematics in Lean_](https://leanprover-community.github.io/mathematics_in_lean/) by Jeremy Avigad and Patrick Massot: if there is something like an official course maintained by experts in charge, this is probably it. It is mainly concentrated about different areas of mathematics.

## Some notes on Lean and Mathlib

* Hardware requirements: In fact, Lean will require a decent hardware, e.g. at least 8GB of RAM in order to function properly. If you do not have this, there are ways of using Lean online; see xxx.
* Lean is not only an interactive theorem prover, but also a programming language. If you want to know/learn more about this aspect, please consult [Functional programming in Lean](https://lean-lang.org/functional_programming_in_lean/).
* While `Lean` is a programming language, `Mathlib` is a library in the Lean language. It collects various (more or less deep) mathematical results. In this course, we do not make any distinction between `Lean` and `Mathlib`, since we will have
```
import Mathlib
```
at the start of any file. In this way, we have access to a large part of mathematics in order to solve exercises.


## How to use this course

These notes have three main parts:

* These introductory notes: Starting in the next chapter, we give general hints on Lean, which are rather for reference and background than for starting the course. You will almost certainly find yourself asking fundamental things on Lean (e.g. _What is type theory, and why should I care?_), which we try to explain without too much detail.
* Tactics descriptions: When interactively writing proofs, a main focus will be the currently _proof state_. In order to modify it, we need tactics, which in some sense feels like learning a new language (which is in fact true). In the latter part of these notes, we give an overview of the most important tactics. A more comprehensive overview is [here](https://github.com/haruhisa-enomoto/mathlib4-all-tactics/blob/main/all-tactics.md).
* The exercises: As in most mathematical courses, the heart are the exercises you have to solve; see the _Exercises_ folder within this repository. Unlike in other courses, you will get immediate feedback of how well you performed on any single exercise. If you want to start right away, please start immediately with the first exercise sheet. More explanations will be given within the exercise sheets.

While the exercises will only cover the first half of the semeser, individual assignments will happen in the latter part of this course. (These will mostly be self-assigned, so e.g. you will formalize an esxercise from your first year of studies, or you are interested in a specific part of `Mathlib`, or...)


# First steps using logic

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

## Natural numbers
To get a little more mathematical, we now introduce the natural numbers. This type (abbreviated `ℕ`, type `\N`) is defined (see 02-a.lean) so that `0 : ℕ` and `succ (n : ℕ) : ℕ`, i.e. with `n` is also `succ n` a natural number. `succ n` stands for the successor of `n`. Furthermore, we will get to know the types `set ℕ` and `Finset ℕ` here. These are the subsets of `ℕ` and the finite subsets of `ℕ`.
-  Sheet 02-a: Natural numbers and the `calc` mode:
    After an introduction to how natural numbers are implemented in `Lean`, we introduce the `calc` mode. This allows us to perform calculations step by step, using previously proven statements. This way, we can, for example, prove binomial formulas. We also get to know the very powerful tactics `ring`, `norm_num`, `linarith` and `simp` can simplify a lot of work. Here we also learn the `fun` notation for defining functions.
-  Page 02-b: divisibility:
    For `m n : ℕ` (or `m n : ℤ`) `h : m | n` (type `\|`), means that `n` is divided by `m`. In other words, there is `a : ℕ` with `n = a * m`. With this definition, the goal of this sheet is to show the long known statement that a number is exactly divisible by 3 (or 9) if and only if its cross sum is divisible by 3 (or 9). Here we will only do this for numbers up to `10000`.
**Bonus task:** An especially simple method of proving the divisibility rule by 3 in Lean is with the following Lean file (here, `\%` is the modulo sign and `digits 10` is the finite list of decimal representations of the
  number `n`):
  ```
    open Nat
    example (n : ℕ) : 3 ∣ n ↔ 3 ∣ (digits 10 n).sum := by
      refine dvd_iff_dvd_digits_sum 3 10 _ n
      norm_num
  ```
This proof is based on the following statement:
```
lemma dvd_iff_dvd_digits_sum (b b' : ℕ) (h : b' % b = 1) (n : ℕ) :
b ∣ n ↔ b ∣ (digits b' n).sum
```
Give a script proof of this statement.
-  Page 02-c: `\sqrt 2`:
     This is about the proof `√2 ∉ ℚ`. Here is the proof as you would find it in a script (or school book): Assuming that there are `m` and `n` such that `√2 = m/n`, then  `2n² = m²`. Let `m` and `n` be relatively prime. Then `2 ∣ m²`. Since `m²` is even, `m` must also be even, so `m = 2a` for some `a`. Thus `2*n² = 4 * a²` or `n² = 2 a²`. This means that `n²` is even, and as just argued, `n` would then be even. However, this contradicts the complementary division of `m` and `n`. This proof is formalized here. (Note that the proof given here only works for `√2`, but not for `√3`. The reason is that we use that for every `m ∈ ℕ` either `m` or `m+1` is even (i.e. divisible by 2). This is obviously false for `3`.)
-  Page 02-d: induction
    induction has been known since the first semester: If one shows for a statement `P : ℕ → Prop` both `P 0` and also `∀ d : ℕ, P d → P (d + 1)`, then one has `∀ n : ℕ, P n` shown. This is the so-called *weak*    induction that we will use here for a few statements. We will also show the well-ordering principle of `ℕ`, which states that every non-empty subset of ℕ contains a smallest element
-  Sheet 02-e: Pigeonhole principle
   If you distribute `m` balls among `n<m` drawers, at least two balls end up in the same drawer. In more mathematical terms, there is no injective mapping of an `m`-element set into an `n<m`-element one. To prove this, we first introduce introduce injective mappings and use an induction principle for `Finset`s.

## Real Numbers

We now come to real numbers without looking at their definition (which
uses Cauchy sequences).
-   Sheet 03-a: Lower Bounds on a Set\
   We introduce the set of lower bounds on a set `A \subsets \mathbb R` is introduced. The largest lower bound is then known to be the `\inf A`. To formulate the main result, we also introduce the limit of a sequence. Finally, we prove that `x = \inf A` holds if and only if there is a sequence in `A` that converges to `x`.
-  Page 03-b: The derivative of `x\mapsto x^{n+1}`\
    As is well known, the derivative of `x\mapsto x^{n+1}` is given by     `x\mapsto (n+1)x^n`. To show this, we need the concept of the derivative (here as a sequence limit), as well as the product rule. We will reduce everything to the calculation rules for limits, such as the fact that the limit of the product of two convergent sequences is given by the product of the limits. After this preliminary work, we prove the formula by induction.
# Notes on Lean

In Section 1, we have already dealt with the installation of Lean and `vscode`. Here follows a short, incoherent introduction. We start with a very simple example. The tactics `intro` and `exact` can be found in
Chapter. If we want to prove the statement `P → P` (i.e. `P` implies `P`) we enter the following on the left side in `vscode`:
```
example (P : Prop) : P → P := by
  sorry
```
On the right side, depending on the position of the cursor, you will find the *proof state*. If the cursor is directly after `by`, the *proof state* is seen. It is important to know that behind `⊢` stands the assertion, and everything above are hypotheses. (In the case shown, this is only the fact that `P` is an assertion/proposition.) This representation thus corresponds exactly to the assertion. If the cursor is after the `sorry`, there is now **no goals**, but the `sorry` tactic is only there to prove unproven assertions without further action, and a warning is issued in `vscode`. If you delete the `sorry` and replace it with an `intro hP`, we get
```
P : Prop
hP : P
⊢ P
```
So we have transformed the statement `P → P` into a state where we have to assume `hP : P` and conclude `P`. This can now easily be solved using `assumption`, and the desired **no goals** appears. The `assumption` tactic searches for a hypothesis that is identical to the statement and concludes the proof. The exact  tactic is somewhat different. Here you have to know exactly which hypothesis is meant and can use `exact hP` to conclude the proof.

## Dependent type theory

Lean is a functional programming language (i.e. it actually only consists of functions) and is based on the *dependent type theory*. Types in programming languages like Python are `bool`, `int`, `double` etc. Lean thrives on defining and using your own types. We will see in the course of the course that you can think of the resulting types as sets. The type `ℕ` will be the set of natural numbers, and `ℝ` the set of real numbers. However, `ℕ` actually represents an infinite set that is characterized by containing `0`, and if it contains `n`, then it also contains the successor of `n` (represented by `succ n`). Accordingly, the real numbers are defined by an equivalence relation on Cauchy sequences,  which is quite elaborate. Types can depend on other types, and that is why we speak of *dependent types*. For example, the space `\mathbb R^n` depends on the dimension `n`. As we shall see mathematical statements are also types. Regarding the notation: for sets, we are used to writing `n\in\mathbb N` if `n` is a natural number. In type theory, we write `n : ℕ` and say that `n` is a term (expression) of type `ℕ`. More generally, every expression has a type and when introducing an expression, Lean checks its type. (Incidentally, this can be quite confusing: for example, the statement `(x : ℕ) → (x : ℤ)`, i.e. (every natural number is also an integer) is not at all comprehensible for `lean`. Because `x` is a term of type `ℕ` (and thus of no other type), so that `x : ℤ` makes no sense at all for `lean`. The solution is an 'invisible mapping' `coe : ℕ → ℤ`.)

## Universes, Types and Terms

In Lean, there are three levels of objects: universes, types and terms. We are concerned here with the last two. Of particular interest is the type `Prop`, which consists of statements that can be true or false . It includes mathematical statements, so either the hypotheses, or the goal of what is to be proven. A hypothesis in Lean has the form `hP : P`, which means `P` is true, and this statement is called `hP`. It can also mean that `P` is true and `hP` is a proof of `P`. The hypotheses here have names `P Q R S`, and the names of the hypotheses `hP hQ hR hS`. All names can be arbitrary. Furthermore, there are hypotheses of the form `P → Q`, which is the statement that `P` implies `Q`.

## Function definitions
In `Lean`, for example, the function `f : \mathbb N \to \mathbb N, x \mapsto 2x` is defined as
```
  f : ℕ → ℕ := fun x ↦ 2*x
```
or
```
fun x ↦ 2*x
```
(Write `\mapsto` for `↦`.) It is assumed that the `x` is only introduced to
define `f`. The application of `f` to an `x : ℕ` is then done using `f x`. (The notation `f x` is an abbreviation for `f(x)`, since `Lean` is sparing with parenthesis.)

## Equality
In Lean, there are three types of equality:

- Syntactic equality: If two terms are letter-for-letter equal, then they are syntactically equal. However, there are a few more situations in which two terms are syntactically equal. Namely, if one term is just an abbreviation for the other (for example, 'x=y' is an abbreviation for 'eq x y'), then these both terms are syntactically equal. Also equal are terms in which globally quantified variables have different letters. For example, `∀ x, ∃ y, f x y` and `∀ y, ∃ x, f y x` are syntactically equal.

- Definitional equality: Some terms are by definition equal in Lean. For `x : ℕ`, `x + 0` is by definition identical to `x`. However, `0 + x` is not   definitionally identical to `x`. This is apparently only due to the     internal definition of addition of natural numbers in Lean.
- Propositional equality: If there is a proof of `x = y`, then `x` and `y` are said to be propositionally equal. Similarly, terms `P` and `Q` are said to be propositionally equal if you can prove `P ↔ Q`. Some Lean Tactics only work up to syntactic equality (such as `rw`), others (most) work up to definitional equality (such as `apply`, `exact`,...) This means that the tactic automatically transforms terms if they are syntactically or definitional equality. There is a special kind of equality to be observed with sets and functions. For example, two functions are exactly the same if they return the same value for all values in the domain. This behavior is called *extensionality* in the theory of programming languages. (If extensionality applies, then, for example, two sorting algorithms are the same if they always produce the same result).

## Different parentheses in `Lean`

There are (essentially) three different types of parentheses in `Lean` statements. The simplest is `(...)`, which, as in normal use, indicates parentheses in the sense of what belongs together. However, you have to learn how 'Lean' brackets internally when no '()' are given. Operators like *and* (`∧`), *or* (`∨`), are right-associative, so e.g. `P ∧ Q ∧ R := P ∧ (Q ∧ R)`. The application of functions in sequence, such as `f : ℕ → ℝ` and `g : : ℝ→ ℝ `, applied to `n : ℕ` is `g (f n)`, because `g` expects an input of type `ℝ`, and this is what `f n` provides. You cannot omit (...), i.e. in this case the parenthesis is left-associative.

Now let's comment on the parentheses `[...]` and `{...}`. For example, `#check@ gt_iff_lt` (the statement that `a>b` holds if and only if `b<a` holds), where both types occur. This yields
```
gt_iff_lt : ∀ {α : Type u_1} [_inst_1 : has_lt α] {a b : α}, a > b ↔ b < a
```

When this result is applied, the statements in `{...}` and `[...]` are added by `Lean` itself. The statements in `{...}` depend on the type of the objects that have to be given, and can therefore be inferred. (Above, when applying `gt_iff_lt`, the variables `a` and `b` have to be given.) Therefore, their type is also known, and one does not have to `α` is not explicitly specified. Since the application is made to a concrete `α` (for example, `ℕ`), and `Lean` knows a lot about the natural numbers, the type class system can look up many properties of `ℕ`, and also finds that `has_lt ℕ` holds (i.e. on `ℕ` at least a partial order is defined).

## Names of `Mathlib` Results

Names like `zero_add, add_zero, one_mul, add_assoc, succ_ne_zero, lt_of_succ_le,...` seem cryptic. It is clear that individual relatively understandable abbreviations (`zero, one, mul, add, succ,...`) are separated by `_`. In general, the following two rules apply to naming:

- The goal of the statement to be proven is described; if hypotheses are added in the name, then with `of_`. The statement `lt_of_succ_le` is therefore an `<` statement, where `succ ≤` applies. In fact:
```
#check @lt_of_succ_le
```
results in
```
  lt_of_succ_le : ∀ {a b : ℕ}, a.succ ≤ b → a < b
```
This way, you can often guess the names of statements that you want to use.




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
