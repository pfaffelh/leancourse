import Lean
import VersoManual
import DemoTextbook
import UsersGuide.Markup
import Manual.Meta.Table
import Leancourse.Misc.Defs

open Verso.Genre Manual
open DemoTextbook.Exts

set_option pp.rawOnError true

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


# Some notes on Lean

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
example (hPQR : P → Q → R) : R := by
  apply hPQR
  · sorry
  · sorry
```


**Remarks:**
* `apply` works up to equality by definition. This can be seen in the example above, where `¬P ↔ (P → False)` is true by definition.
* `apply h` is frequently identical to `refine ?_`.
* If the use of `apply` closes the current goal, you might as well use `exact` instead of `apply`.


## `by_cases`

**Summary:**
If you have a term `P : Prop` as a hypothesis, `by_cases hP : P` returns two goals. The first one has `hP : P`, and the second one `hP : ¬P`. This tactic is thus identical to `have hP : P ∨ ¬ P, exact em P, cases hP,`. (The second expression is `em : ∀ (p : Prop), p ∨ ¬p`.)

**Examples**


In the second example, we use a variable of type `bool` This is defined as follows:

```
inductive bool : Type
| ff : bool
| tt : bool
```

A Boolean variable can only have the values `tt` (for `true`) and `ff` (for `false`).

**Notes**

* Apparently, the `by_cases` tactic (just like `by_contradiction`) assumes that a statement is either true or false. This is also known as the law of excluded middle. In mathematics, proofs that do not use this rule are called constructive.
* For terms of type `Prop`, the tactic `tauto` (or `tauto!`) can
draw

## `by_contra`

**Summary**

The `by_contra` tactic provides a proof by contradiction. It is therefore assumed (i.e. transformed into a hypothesis) that the statement (after `⊢`) is not true, and this must be made to contradict itself, i.e. a proof of `false` must be found.

**Examples**

+---------------------------+-----------------------+-----------------------+
| **Proof state** | **Command** | **New proof state** |
+:==========================+:======================+:======================+
| `⊢ P` | `by_contra h,` | `h : ¬P` |
+---------------------------+-----------------------+-----------------------+
| | | `⊢ false` |
+---------------------------+-----------------------+-----------------------+
| `h: ¬¬P`\ | | |
| `⊢ P` | | |
| | | |
| & | | |
| | | |
| `by_contra hnegP,` | | |
| | | |
| & | | |
| | | |
| `h: ¬¬P`\ | | |
| `hnegP: ¬P`\ | | |
| `⊢ false` | | |
+---------------------------+-----------------------+-----------------------+

**Notes**

This tactic is stronger than `exfalso`. After all, there the goal is only converted to `false` without adding a new hypothesis. With `by_contra`, the new goal is also `false`, but there is still a new hypothesis.

## `calc`

**Summary:** As the word suggests, `calc` is about concrete calculations. This is not a tactic, but a `lean` mode. This means that you can enter this mode (with the word `calc`) and enter calculation steps and proofs that each individual calculation step is correct.

**Examples**

Here is a proof of the first binomial formula that only comes about by rewriting of calculating properties from the `mathlib`.

```
example (n : ℕ): (n+1)^2 = n^2 + 2*n + 1 := by
have h : n + n = 2*n,
{
nth_rewrite 0 ← one_mul n,
nth_rewrite 1 ← one_mul n,
rw ← add_mul,
},
calc (n+1)^2 = (n+1) * (n+1) : by { rw pow_two, }...
 = (n+1)*n + (n+1) * 1: by {rw mul_add, }
... = n*n + 1*n + (n+1) : by {rw add_mul, rw mul_one (n+1),}...
 = n^2 + n + (n+1) : by {rw one_mul, rw ← pow_two,}
... = n^2 + (n + n+1) : by {rw add_assoc, rw ← add_assoc n n 1,}...
 = n^2 + 2*n + 1 : by { rw ← add_assoc, rw ← h, },
```

The same can be achieved without the `calc` mode, like this:

```
example (n : ℕ): (n+1)^2 = n^2 + 2*n + 1 := by
  have h : n + n = 2*n, by { nth_rewrite 0 ← one_mul n,
  nth_rewrite 1 ← one_mul n, rw ← add_mul, },
  rw [pow_two, mul_add, add_mul, mul_one (n+1), one_mul,
  ← pow_two, add_assoc, ← add_assoc n n 1,
  ← add_assoc, ← h],
```

However, this is much less readable.

**Notes**

## `cases`

**Summary:** If a hypothesis is composed, i.e. can be expanded into two or more cases, `cases'` delivers exactly that. This can be used not only used with hypotheses `h : P ∨ Q` or `h : P ∧ Q`, but also with structures that consist of several cases, such as `∃...` (here there is a variable and a statement) and `x : bool` or `n : ℕ`.

**Examples:**


**Notes:**

* The application `cases' n` for `n : ℕ` is strictly weaker than complete induction (see `induction`). After all, `cases` only converts `n : ℕ` into the two cases `0` and `succ n`, but you cannot use the statement for `n-1` to prove the statement for `n`.
* A more flexible version of `cases'` is `rcases`.

## `change`

**Summary:**

Changes the goal (or a hypothesis) into a goal (or a hypothesis) that is defined the same.

**Examples:**

+---------------------------------+---------------------+-----------------------+
| **Proof state** | **Command** | **New proof state** |
+:================================+:====================+:======================+
| `⊢ : P → false` | `change ¬P,` | `⊢ ¬P` |
+---------------------------------+---------------------+-----------------------+
| `h : ¬P`\ | | |
| `⊢ Q` | | |
| | | |
| & | | |
| | | |
| `change P → false at h,` | | |
| | | |
| & | | |
| | | |
| `h: P → false`\ | | |
| `⊢ Q` | | |
+---------------------------------+---------------------+-----------------------+

**Notes:**

* As can be seen from the penultimate example, `change` also works for hypotheses.
* Since many tactics test for definitional equality anyway, `change` is often not necessary. However, it can help to make the proof more readable.

## `clear`

**Summary:** With `clear h` the hypothesis `h` is removed from the goal state
(forgotten).

**Examples:**

**Proof state** **Command** **New proof state**
----------------- ------------------- -----------------------
`h : P` `clear h,` `⊢ Q`
`⊢ Q`

## `congr`

**Summary:** If you have to show an equality `f x = f y`, then `congr` uses the statement that the equality is particularly true if `x = y`.

**Examples:**

**Proof state** **command** **New proof state**
---------------------- ----------------- -----------------------
`⊢ P x = P y` `congr,` `⊢ x = y`

**Notes:**

The related tactic `congr'` uses another parameter that determines how many recursive layers are eliminated in the goal. This is helpful in the following examples:



+----------------------------------+--------------+-----------------------+
| **Proof state** | **Command** | **New proof state** |
+:=================================+:=============+:======================+
| `⊢ f (x + y) = f (y + x)` | | |
| | | |
| & | | |
| | | |
| `congr,` | | |
| | | |
| & | | |
| | | |
| `⊢ x = y`\ | | |
| `⊢ y = x` | | |
+----------------------------------+--------------+-----------------------+

## `exact`

**Summary:** If the goal can be achieved with a single command, then it can be achieved with the `exact` tactic. Like many other tactics, `exact` also works with terms that are defined the same.

**Examples:**

+----------------------------+-------------------+-------------------------+
| **Proof state** | **Command** | **New proof state** |
+:===========================+:==================+:========================+
| `h : P` | `exact h,` | **goals accomplished** |
+----------------------------+-------------------+-------------------------+
| `⊢ P` | | |
+----------------------------+-------------------+-------------------------+
| `hP: P`\ | | |
| `hQ: Q`\ | | |
| `⊢ P ∧ Q` | | |
| | | |
| & | | |
| | | |
| `exact ⟨ hP, hQ ⟩,` | | |
| | | |
| & | | |
| | | |
| **goals accomplished** | | |
+----------------------------+-------------------+-------------------------+

**Notes:**

In the third example, note the order in which the two hapotheses `hP` and `hnP` are applied. The first hypothesis after `exact` is always the one whose right side matches the goal. If the goal requires further input, it is appended afterwards.

## `exfalso`

**Summary:** The statement `false → P` is true for all `P`. If the current goal is `⊢ P`, and you would apply this true statement using `apply`, the new goal would be `⊢ false`. This is exactly what the `exfalso` tactic does.

**Examples:**

+--------------------+-------------------+-----------------------+
| **Proof state** | **Command** | **New proof state** |
+:===================+:==================+:======================+
| `h : P` | `exfalso,` | `h : P` |
+--------------------+-------------------+-----------------------+
| `⊢ Q` | | `⊢ false` |
+--------------------+-------------------+-----------------------+
| `hP: P`\ | | |
| `hnP: ¬P`\ | | |
| `⊢ Q` | | |
| | | |
| & | | |
| | | |
| `exfalso, ` | | |
| | | |
| & | | |
| | | |
| `hP: P`\ | | |
| `hnP: ¬P`\ | | |
| `⊢ false` | | |
+--------------------+-------------------+-----------------------+

**Notes:**

If you use this tactic, you leave the realm of constructive mathematics. (This dispenses with the rule of the excluded middle.)

## `have`

**Summary:** By using `have` we introduce a new claim, which we have to prove first. Afterwards, it is available as a hypothesis in all further goals. This is identical to first proving a lemma `h` with the statement after `have h : ` and then reusing it at the appropriate place in the proof (for example with `apply` or `rw`).

**Examples:**

+----------------------+----------------------+----------------------+
| **Proof state** | **Command** | **New proof |
| | | state** |
+:=====================+:=====================+:=====================+
| `⊢ R` | `have | `⊢ P ↔ Q` |
| | h : P ↔ Q, ` | |
+----------------------+----------------------+----------------------+
| | | `h : P ↔ Q` |
+----------------------+----------------------+----------------------+
| | | `⊢ R` |
+----------------------+----------------------+----------------------+
| `⊢ P` | | |
| | |
| & | | |
| | | |
| `have h1 : | | |
| ∃ (m : ℕ),`\ | | |
| ` | | |
| f 27 m, ...`\ | | |
| `cases | | |
| h1 with m hm` | | |
| | | |
| & | | |
| | | |
| `m : ℕ`\ | | |
| `hm: f 27 m`\ | | |
| `⊢ P` | | |
+----------------------+----------------------+----------------------+

**Notes:**

* Suppose we have two goals (let's call them `⊢1` and `⊢2`), and we need the statement of `⊢1` in the proof of `⊢2`. We can first introduce a third goal with `have h := ⊢ 1` (where `⊢1` is to be replaced by the statement). Then `⊢ 1` can be proved with `exact`, and has the statement `⊢ 1` available in the proof of `⊢ 2`.

## `induction`

**Summary:**

Inductive types allow the possibility of proving statements about them by means of induction. This includes, for example, the usual case of complete induction over natural numbers.

**Examples**

**Proof state** **command** **new proof state**
---------------------- --------------------------------- ---------------------------------
`n : ℕ` `induction n with d hd,` `⊢ 0 = 0 + 0`
`⊢ n = 0 + n` `hd : d = 0 + d`
`⊢ d.succ = 0 + d.succ,`

## `intro`

**Summary**

If the goal is of the form `⊢ P → Q` or `∀ (n : ℕ), P n`, you can proceed with `intro P` or `intro n`. You can use several `intro` commands at the same time to summarize a single one. A little more precisely, `intro h1 h2 h3,` is identical to `intro h1; intro h2; intro h3`.


**Examples**

**Proof state** **Command** **New proof state**
--------------------------- ------------------- -----------------------
`⊢ P → Q` `intro hP` `hP : P`
`⊢ Q`
`f : α → Prop` `intro x,` `f: α → Prop`
`⊢ ∀ (x : α), f x` `x : α`
`⊢ f x`

+-------------------------------+------------------------+-----------------------+
| **Proof state** | **Command** | **New proof state** |
+:==============================+:=======================+:======================+
| `⊢ P → Q → R` | `intros hP hQ,` | `hP : P` |
+-------------------------------+------------------------+-----------------------+
| | | `hQ : Q` |
+-------------------------------+------------------------+-----------------------+
| | | `⊢ R` |
+-------------------------------+------------------------+-----------------------+
| `P: ℕ → Prop`\ | | |
| `⊢ ∀ (n : ℕ), P n → Q` | | |
| | | |
| & | | |
| | | |
| `intros n hP` | | |
| | | |
| & | | |
| | | |
| `P: ℕ → Prop`\ | | |
| `n: ℕ`\ | | |
| `hP: P n` `⊢ Q` | | |
+-------------------------------+------------------------+-----------------------+


**Notes**

* Several `intro` commands in a row are best combined. Furthermore,  `rintro` is a more flexible variant.
* A reversal of `intro` is `revert`.






## `left`

**Summary:**

The application of `left,` is identical to `apply h` for `h : P → P ∨ Q`. So if you have a goal of the form `⊢ P ∨ Q`, `left,` causes you to have only the goal `⊢ P`. After all, it is sufficient to show `P` to close the goal.

**Examples:**

+-------------------------+----------------+-----------------------+
| **Proof state** | **Command** | **New proof state** |
+:========================+:===============+:======================+
| `⊢ P ∨ Q` | `left,` | `⊢ P` |
+-------------------------+----------------+-----------------------+
| `⊢ ℕ` | | |
| | | |
| & | | |
| | | |
| `left,` | | |
| | | |
| & | | |
| | | |
| **goals accomplished** | | |
+-------------------------+----------------+-----------------------+


The second example requires a little explanation. First of all, you have to understand that the goal `⊢ ℕ` is to show that there is a term of type `ℕ`, i.e. that there is a natural number. Now you have to know how `ℕ` is implemented in Lean. This is

```
inductive nat
| zero : nat
| succ (n : nat) : nat
```

together with

```
notation `ℕ` := nat
```
This means: The type `ℕ` is defined by the fact that `zero` is a term of this type, and that there is a function `succ : ℕ → ℕ`. Thus, in the second example, the input `left,` is closed because by definition `zero : ℕ` holds, so in particular there is a term of type `ℕ`.

**Notes:**

* See also `right,` for the equivalent tactic, which is `apply h` for `h : Q → P ∨ Q`.
* As in the second example, `left,` can always be applied when dealing with an inductive type with two constructors (such like `ℕ`).

## `apply?`

**Summary:** There are already a lot of proven statements in `mathlib`. When using `apply?`, the `mathlib` is statements whose types correspond to those of the statement to be proved. If this is not successful, `Lean` reports a `timeout`. If successful, it also reports which command was found. If you click on it, this is inserted in place of `library_search`.

**Examples**

**Proof state** **Command** **New proof state**
--------------------- -------------------------- -------------------------------
`h1 : a < b` `library_search,` **goals accomplished**
`h2 : b < c` `Try this: `
`⊢ a < c` `exact lt_trans h1 h2`

**Notes**

The tactic `suggest` is similar and also works if
the goal cannot be closed.

## `linarith`

**Summary:** This tactic can prove equations and inequalities with the help of hypotheses. It is important that the hypotheses used are also only equations and inequalities. So here we are working mainly with the transitivity of `<` together with arithmetic rules.

**Examples:**

**Proof state** **Command** **New proof state**
---------------------- -------------------- -------------------------
`h1 : a < b` `linarith,` **goals accomplished**
`h2 : b ≤ c`
`⊢ a < c`

## `norm_num`

**Summary:** As long as no variables are involved, `norm_num` can perform calculations involving `=`, `<`, `≤`, or '≠'.

**Examples:**

+----------------------------+--------------------+-------------------------+
| **Proof state** | **Command** | **New proof state** |
+:===========================+:===================+:========================+
| `⊢ 2 + 2 < 5` | `norm_num,` | **goals accomplished** |
+----------------------------+--------------------+-------------------------+
| `⊢ | (1 : ℝ) | = 1` | | |
| | | |
| & | | |
| | | |
| `norm_num,` | | |
| | | |
| & | | |
| | | |
| **goals accomplished** | | |
+----------------------------+--------------------+-------------------------+

**Notes:**

`norm_num` knows a few other arithmetic operations, such as the absolute value function, see the second example.

## `nth_rewrite`

**Proof state** **Command** **New proof state**
--------------------------- -------------------- -------------------------
`⊢ 2 + 2 < 5` `norm_num,` **goals accomplished**

**Summary:**

This tactic is related to `rw`. The difference is that you can specify the occurrence number of the term to be replaced on which `rw` is to be applied. The exact syntax is `nth_rewrite k h`, where `k` is the number (starting with $0$) of the term to be replaced and `h` is the hypothesis to be replaced. As with `rw`, this must be in the form `h : x=y` or `h : A↔B`.

**Examples:**

+----------------------------------+--------------+-----------------------+
| **Proof state** | **Command** | **New proof state** |
+:=================================+:=============+:======================+
| `n : ℕ`\ | | |
| `⊢ 0 + n = 0 + 0 + n` | | |
| | | |
| & | | |
| | | |
| `nth_rewrite 0 zero_add,` | | |
| | | |
| & | | |
| | | |
| `n: ℕ`\ | | |
| `⊢ n = 0 + 0 + n` | | |
+----------------------------------+--------------+-----------------------+

In the above example, Lean sees three terms of the form `0 + ?_`: Number 0 is on the left-hand side, for numbers 1 and 2, on the right side (because of the parenthesis `0 + 0 + n = (0 + 0) + n`),  the second = is checked first. To the left of it is `0 + 0`, which is by definition identical to `0`. applying `rw zero_add` here, the term is converted to `n`. For number 2, you see `0 + 0`, determine that it is of the desired form and convert it to `0`.

## `obtain`

**Summary:** The `obtain` tactic can be used to merge `have` and `cases` into one command.

**Examples:**

**Proof state** **Command** **New proof state**
------------------------------------------ --------------------------- -------------------------------------
`f : ℕ → ℕ → Prop` `obtain ⟨ m, hm ⟩` `f: ℕ → ℕ → Prop`
`h : ∀ (n : ℕ), ∃ (m : ℕ), f n m` ` := h 27,` `h : ∀ (n : ℕ), ∃ (m : ℕ), `
` f n m`
`m : ℕ`
`hm : f 27 m`

## `push_neg`

**Summary:** In many steps of a proof, a negation must be carried out. In order to process the corresponding quantifiers etc. as well and to better reusable, the tactic `push_neg` is available.

**Examples**
+---------------------+--------------+-----------------------+
| **Proof state** | **Command** | **New proof state** |
+:====================+:=============+:======================+
| `⊢ ¬(P ∨ Q)` | | |
| | | |
| & | | |
| | | |
| `push_neg,` | | |
| | | |
| & | | |
| | | |
| `⊢ ¬P ∧ ¬Q` | | |
+---------------------+--------------+-----------------------+

**Notes:**

This tactic also works with other objects, such as sets.

## `rcases`

+-------------------------------+--------------+-----------------------+
| **Proof state** | **Command** | **New proof state** |
+:==============================+:=============+:======================+
| `h : P ∧ Q ∨ P ∧ R`\ | | |
| `⊢ P` | | |
| | | |
| & | | |
| | | |
| `rcases h with`\ | | |
| `(⟨hP1,hQ⟩|⟨hP2,hR⟩),` | | |
| | | |
| & | | |
| | | |
| `hP1 : P`\ | | |
| `hQ : Q`\ | | |
| `⊢ P`\ | | |
| `hP2 : P `\ | | |
| `hR : R`\ | | |
| `⊢ P` | | |
+-------------------------------+--------------+-----------------------+

**Summary:** `rcases` is a more flexible version of `cases`. Here, it is allowed to use `⟨ hP, hQ ⟩` (or `(hP | hQ)`) to to split the hypotheses `hP` and `hQ` into their cases.  As can be seen in the example above, it is also possible to nest `⟨.,.⟩` and `(.|.)`.

**Examples:**

+----------------------------+--------------+-----------------------+
| **Proof state** | **Command** | **New proof state** |
+:===========================+:=============+:======================+
| `h : P ∧ Q`\ | | |
| `⊢ R` | | |
| | | |
| & | | |
| | | |
| `rcases h with`\ | | |
| ` ⟨ hP, hQ ⟩` | | |
| | | |
| & | | |
| | | |
| `hP : P`\ | | |
| `hQ : Q`\ | | |
| `⊢ R` | | |
+----------------------------+--------------+-----------------------+

**Notes:**

The last example shows how to use `rcases` to directly resolve a `∃` quantifier in a hypothesis that has more than one constraint (here: `0 ≤ m)` and `m < n` can be resolved directly.

## `refine`

**Summary:** The `refine` tactic is like `exact` with holes. More precisely: if the goal is to apply a combination of hypotheses, you can do that with 'refine' and write an open term '_' for each. You then get each '_' back as a new goal (where those with definitional equality are solved immediately).

**Examples:**

+----------------------+----------------------+----------------------+
| **Proof state** | **Command** | **New proof |
| | | state** |
+:=====================+:=====================+:=====================+
| `hQ : Q` | `refin | `hQ : Q` |
| | e ⟨ _, hQ ⟩,` | |
+----------------------+----------------------+----------------------+
| `⊢ P ∧ Q` | | `⊢ P` |
+----------------------+----------------------+----------------------+
| `⊢ ∃ (n : ℕ) (h | | |
| : n > 0), `\ | | |
| ` | | |
| n ^ 2 = 9` | | |
| | | |
| & | | |
| | | |
| `refine `\ | | |
| `⟨3, ?_, b | | |
| y norm_num⟩,` | | |
| | | |
| & | | |
| | | |
| `⊢ 3 > 0` | | |
+----------------------+----------------------+----------------------+

## `refl`

**Summary:** This tactic proves the equality (or equivalence) of two definitionally equal terms.

**Examples:**

+-------------------------+----------------+-------------------------+
| **Proof state** | **Command** | **New proof state** |
+:========================+:===============+:========================+
| `⊢ P ↔ P` or | `refl,` | **goals accomplished** |
+-------------------------+----------------+-------------------------+
| `⊢ P = P` | | |
+-------------------------+----------------+-------------------------+
| `⊢ 1 + 2 = 3` | | |
| | | |
| & | | |
| | | |
| `refl,` | | |
| | | |
| & | | |
| | | |
| **goals accomplished** | | |
+-------------------------+----------------+-------------------------+

**Notes:**

The second example works because both sides are by definition equal to `succ succ succ 0`.

## `revert`

**Summary:** `revert` is the opposite of `intro`: It takes a hypothesis from the local context and inserts it as a precondition into the goal.

**Examples**

+--------------------+--------------+-----------------------+
| **Proof state** | **Command** | **New proof state** |
+:===================+:=============+:======================+
| `hP : P`\ | | |
| `⊢ Q` | | |
| | | |
| & | | |
| | | |
| `revert hP` | | |
| | | |
| & | | |
| | | |
| `⊢ P → Q` | | |
+--------------------+--------------+-----------------------+

**Notes:**

`revert` is rarely needed; actually only when you want to apply an already proven result exactly and first want to establish the correct form of the goal.

## `right`

**Summary:** See `left`, where the adjustments are obvious.

**Examples**

**Proof state** **command** **New proof state**
------------------ ----------------- -----------------------
`⊢ P ∨ Q` `right,` `⊢ Q`

## `ring`

**Summary:** The `ring` uses rules of calculation such as associativity, commutativity, and distributivity to achieve the goal.

**Examples**

+------------------------------------+----------------+-------------------------+
| **Proof state** | **Command** | **New proof state** |
+:===================================+:===============+:========================+
| `x y : ℝ` | `ring,` | **goals accomplished** |
+------------------------------------+----------------+-------------------------+
| `⊢ x + y = y + x` | | |
+------------------------------------+----------------+-------------------------+
| `n : ℕ`\ | | |
| `⊢ (n+1)^2 = n^2 + 2*n + 1` | | |
| | | |
| & | | |
| | | |
| `ring,` | | |
| | | |
| & | | |
| | | |
| **goals accomplished** | | |
+------------------------------------+----------------+-------------------------+

**Notes:**

* The second example works even though `ℕ` is not a ring (but only a half-ring). It would also work with `n : ℝ` (since `ℝ` has more calculation rules than `ℕ`).
* `ring` is only used to close the goal.


## `rintro`

**Summary:** The `rintro` tactic is used to process several `intro` and `cases` tactics on one line.

**Examples**

**Proof state** **Command** **New proof state**
---------------------- ------------------------------ -----------------------
`⊢ P ∨ Q → R` `rintro ( hP | hQ ),` `hP : P`
$=$ `⊢ P`
`intro h,` `hQ : Q`
`cases h with hP hQ,` `⊢ Q`
`⊢ P ∧ Q → R` `rintro ⟨ hP , hQ ⟩,` `hP : P`
$=$ `hQ : Q`
`intro h,` `⊢ Q`
`cases h with h1 h2,`

**Notes:**

Here, more than two `∨` can also be split into cases in one step: With `A ∨ B ∨ C`, `rintro (A | B | C)` introduces three goals.

## `rw`

**Summary:** `rw` stands for *rewrite*. For `rw h` to work, `h` must be an expression of the type `h : x=y` or `h : A↔B`. In this case, `rw h`  replaces every term that is syntactically identical to `x` (or `A`) is replaced by `y` (or `B`). This also works if `h` is an already proven result (i.e. a `lemma` or `theorem`). With `rw ← h` is applied from right to left. (In the above example, `y` is replaced by `x` and `B` by `A`.)

**Examples**

For the last four examples, you first need to know that add_comm and add_zero are the statements
```
add_comm : ∀ {G : Type} [_inst_1 : add_comm_semigroup G] (a b : G),
a + b = b + a
add_zero : ∀ {M : Type} [_inst_1 : add_zero_class M] (a : M), a + 0 = a
```

In the first of the four examples, `rw` applies to the first occurrence of a term of type `a + b`. Due to the internal bracketing, `(k + m) + 0` is on the left side, so that the `rw` results in a `0 + k + m`. If you want to use the commutativity in the term `k + m`, you need the second (or third) example, where `rw add_comm k m` leads to the desired progress. In the last example, the two `+ 0` terms are first eliminated by `rw add_zero`.

**Notes**

* `rw` is used very often in practice to apply statements from the `mathlib` (at least if they are of the type `=` or `↔`).
* If you want to combine several `rw` commands, you can do so in square brackets, for example `rw [h1, h2]` or `rw [h1, ←h2, h3]`.
* `rw` immediately executes a `refl` after its application. This leads to the second and third examples of the applications of `add_comm` and `add_zero` that the new proof state is not as specified, but **no goals**.
* If you do not want to perform a `rw` in sequence (as in the double elimination of the `+0` above), you can use `nth_rewrite` to rewrite the second occurrence of a term.
* The `rw` tactic does not work when it comes after a *binder*, which could be a `∀ ∃ ∑`. In this case, `simp_rw` will hopefully help.

## `simp`

**Summary:** In `mathlib` there are many lemmas with `=` or `↔` statements that can be applied with `rw` and are marked with `@[simp]`. These marked lemmas have the property that the right side is a simplified form of the left side. With `simp`, `lean` looks for matching lemmas and tries to apply them.

**Examples**


**Notes:**

If you want to know which lemmas were used, try 'simp?` or 'squeeze_simp`. This provides clues.

+---------------------------------+--------------+-----------------------+
| **Proof state** | **Command** | **New proof state** |
+:================================+:=============+:======================+
| `⊢ n + 0 = n` | | |
| | | |
| & | | |
| | | |
| `simp?,` | | |
| | | |
| & | | |
| | | |
| **goals accomplished**\ | | |
| Try this:\ | | |
| `simp only [add_zero, `\ | | |
| ` eq_self_iff_true]` | | |
+---------------------------------+--------------+-----------------------+

## `specialize`

**Proof state** **Command** **New proof state**
----------------------------- --------------------------- -----------------------
`f : ℕ → Prop` `specialize h 13,` `f: ℕ → Prop`
`h : ∀ (n : ℕ), f n` `h : f 13`
`⊢ P` `⊢ P`

**Summary:** In a hypothesis `h : ∀ n, ...`, `...` applies to all `n`, but for the proof of the goal, you may only need a specific `n`. If you specify `specialize h` followed by the value for which `h` is needed, the hypothesis changes accordingly.

**Examples**

+-----------------------------------+--------------+-----------------------+
| **Proof state** | **Command** | **New proof state** |
+:==================================+:=============+:======================+
| `h: ∀ (n : ℕ), 0 < n + 1`\ | | |
| `⊢ 0 < 1` | | |
| | | |
| & | | |
| | | |
| `specialize h 0,` | | |
| | | |
| & | | |
| | | |
| `m : ℕ`\ | | |
| `h: 0 < 0 + 1`\ | | |
| `⊢ 0 < 1` | | |
+-----------------------------------+--------------+-----------------------+

**Notes**

* Just as with `use`, you have to be careful that the goal remains provable.
* If you want to use two values of the hypothesis `h`, then `let h' := h` first provides a duplication of the hypothesis, so that you can then apply `specialize` to `h` and `h'`.

## `constructor`

**Summary:** If the goal is of the type `⊢ P ∧ Q`, it is replaced by `constructor` into two goals `⊢ P` and `⊢ Q`.

**Examples**

**Proof state** **Command** **New proof state**
------------------ ----------------- -----------------------
`⊢ P ∧ Q` `split,` `⊢ P`
`⊢ Q`
`⊢ P ↔ Q` `split,` `⊢ P → Q`
`⊢ Q → P`

**Notes**

Note that `⊢ P ↔ Q` is identical to `⊢ (P → Q) ∧ (Q → P)`.

## `tauto`

**Summary:** `tauto` solves all goals that can be solved with a truth table.

**Examples**

+----------------------+----------------------+----------------------+
| **Proof state** | **Command** | **New proof |
| | | state** |
+:=====================+:=====================+:=====================+
| `⊢ P | `tauto,` or | **goals accomplished |
| ∧ Q → P` | `tauto!,` | ** |
+----------------------+----------------------+----------------------+
| `⊢ ((P → | | |
| Q) → P) → P` | | |
| | | |
| & | | |
| | | |
| `tauto!, ` | | |
| | | |
| & | | |
| | | |
| **goals accomplished | | |
| ** | | |
+----------------------+----------------------+----------------------+

The truth tables for `¬P`, `P ∧ Q` and `P ∨ Q` are as follows; if more terms of type `Prop` are involved, there are more lines.

::: center
`P` `¬P`
---------------- ----------------
`true` `false`
`false` `true`

`P` `Q` `(P ∧ Q)`
---------------- ---------------- ------------------
`true` `true` `true`
`false` `true` `false`
`true` `false` `false`
`false` `false` `false`

`P` `Q` `(P ∨ Q)`
---------------- ---------------- ------------------
`true` `true` `true`
`false` `true` `true`
`true` `false` `true`
`false` `false` `false`
:::

**Notes**

The difference between `tauto` and `tauto!` is that in the latter tactic, the rule of the excluded middle is allowed.  The second example can therefore only be solved with `tauto!`, but not with `tauto`.

## `triv`

**Summary**

`triv` solves an objective that is, by definition, identical to `true`. It also solves objectives that can be solved with `refl`
.

**Examples**

+-------------------------+----------------+-------------------------+
| **Proof state** | **Command** | **New proof state** |
+:========================+:===============+:========================+
| `⊢ true` | `triv,` | **goals accomplished ** |
+-------------------------+----------------+-------------------------+
| `⊢ x=x` | | |
| | | |
| & | | |
| | | |
| `triv,` | | |
| | | |
| & | | |
| | | |
| **goals accomplished ** | | |
+-------------------------+----------------+-------------------------+

## `use`

**Proof state** **Command** **New proof state**
--------------------------- ----------------- -----------------------
`f : α → Prop` `use y,` `f : α → Prop`
`y : α` `y : α`
⊢ ∃ (x : α), f x` ⊢ f y`

**Summary:** The `use` tactic is used for goals that begin with ∃. Here, parameters are used to indicate which object quantified by ∃ is to be reused in the proof.

**Examples**

+----------------------------------+--------------+-----------------------+
| **Proof state** | **Command** | **New proof state** |
+:=================================+:=============+:======================+
| `⊢ ∃ (k : ℕ), k * k = 16` | | |
| | |
| & | | |
| | |
| `use 4, ` | | |
| | | |
| & | | |
| | | |
| `⊢ 4 * 4 = 16` | | |
+----------------------------------+--------------+-----------------------+
