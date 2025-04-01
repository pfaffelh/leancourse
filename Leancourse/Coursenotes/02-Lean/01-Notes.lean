import Lean
import VersoManual
import Manual.Meta
import Leancourse.Misc.Defs

open Verso.Genre Manual

set_option pp.rawOnError true

#doc (Manual) "Notes on Lean" =>
%%%
htmlSplit := .never
tag := "lean"
%%%

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


# Dependent type theory
%%%
tag := "dependent-type-theory"
%%%

Lean is a functional programming language (i.e. it actually only consists of functions) and is based on the *dependent type theory*. Types in programming languages like Python are `bool`, `int`, `double` etc. Lean thrives on defining and using your own types. We will see in the course of the course that you can think of the resulting types as sets. The type `ℕ` will be the set of natural numbers, and `ℝ` the set of real numbers. However, `ℕ` actually represents an infinite set that is characterized by containing `0`, and if it contains `n`, then it also contains the successor of `n` (represented by `succ n`). Accordingly, the real numbers are defined by an equivalence relation on Cauchy sequences,  which is quite elaborate. Types can depend on other types, and that is why we speak of *dependent types*. For example, the space `\mathbb R^n` depends on the dimension `n`. As we shall see mathematical statements are also types. Regarding the notation: for sets, we are used to writing `n\in\mathbb N` if `n` is a natural number. In type theory, we write `n : ℕ` and say that `n` is a term (expression) of type `ℕ`. More generally, every expression has a type and when introducing an expression, Lean checks its type. (Incidentally, this can be quite confusing: for example, the statement `(x : ℕ) → (x : ℤ)`, i.e. (every natural number is also an integer) is not at all comprehensible for `lean`. Because `x` is a term of type `ℕ` (and thus of no other type), so that `x : ℤ` makes no sense at all for `lean`. The solution is an 'invisible mapping' `coe : ℕ → ℤ`.)

# Universes, Types and Terms
%%%
tag := "universes"
%%%

In Lean, there are three levels of objects: universes, types and terms. We are concerned here with the last two. Of particular interest is the type `Prop`, which consists of statements that can be true or false . It includes mathematical statements, so either the hypotheses, or the goal of what is to be proven. A hypothesis in Lean has the form `hP : P`, which means `P` is true, and this statement is called `hP`. It can also mean that `P` is true and `hP` is a proof of `P`. The hypotheses here have names `P Q R S`, and the names of the hypotheses `hP hQ hR hS`. All names can be arbitrary. Furthermore, there are hypotheses of the form `P → Q`, which is the statement that `P` implies `Q`.

# Function definitions
%%%
tag := "functions"
%%%

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

# Equality
%%%
tag := "equality"
%%%

In Lean, there are three types of equality:

- Syntactic equality: If two terms are letter-for-letter equal, then they are syntactically equal. However, there are a few more situations in which two terms are syntactically equal. Namely, if one term is just an abbreviation for the other (for example, 'x=y' is an abbreviation for 'eq x y'), then these both terms are syntactically equal. Also equal are terms in which globally quantified variables have different letters. For example, `∀ x, ∃ y, f x y` and `∀ y, ∃ x, f y x` are syntactically equal.

- Definitional equality: Some terms are by definition equal in Lean. For `x : ℕ`, `x + 0` is by definition identical to `x`. However, `0 + x` is not   definitionally identical to `x`. This is apparently only due to the     internal definition of addition of natural numbers in Lean.
- Propositional equality: If there is a proof of `x = y`, then `x` and `y` are said to be propositionally equal. Similarly, terms `P` and `Q` are said to be propositionally equal if you can prove `P ↔ Q`. Some Lean Tactics only work up to syntactic equality (such as `rw`), others (most) work up to definitional equality (such as `apply`, `exact`,...) This means that the tactic automatically transforms terms if they are syntactically or definitional equality. There is a special kind of equality to be observed with sets and functions. For example, two functions are exactly the same if they return the same value for all values in the domain. This behavior is called *extensionality* in the theory of programming languages. (If extensionality applies, then, for example, two sorting algorithms are the same if they always produce the same result).

# Different parentheses in `Lean`
%%%
tag := "parenthesis"
%%%

There are (essentially) three different types of parentheses in `Lean` statements. The simplest is `(...)`, which, as in normal use, indicates parentheses in the sense of what belongs together. However, you have to learn how 'Lean' brackets internally when no '()' are given. Operators like *and* (`∧`), *or* (`∨`), are right-associative, so e.g. `P ∧ Q ∧ R := P ∧ (Q ∧ R)`. The application of functions in sequence, such as `f : ℕ → ℝ` and `g : : ℝ→ ℝ `, applied to `n : ℕ` is `g (f n)`, because `g` expects an input of type `ℝ`, and this is what `f n` provides. You cannot omit (...), i.e. in this case the parenthesis is left-associative.

Now let's comment on the parentheses `[...]` and `{...}`. For example, `#check@ gt_iff_lt` (the statement that `a>b` holds if and only if `b<a` holds), where both types occur. This yields
```
gt_iff_lt : ∀ {α : Type u_1} [_inst_1 : has_lt α] {a b : α}, a > b ↔ b < a
```

When this result is applied, the statements in `{...}` and `[...]` are added by `Lean` itself. The statements in `{...}` depend on the type of the objects that have to be given, and can therefore be inferred. (Above, when applying `gt_iff_lt`, the variables `a` and `b` have to be given.) Therefore, their type is also known, and one does not have to `α` is not explicitly specified. Since the application is made to a concrete `α` (for example, `ℕ`), and `Lean` knows a lot about the natural numbers, the type class system can look up many properties of `ℕ`, and also finds that `has_lt ℕ` holds (i.e. on `ℕ` at least a partial order is defined).

# Names of `Mathlib` Results
%%%
tag := "names"
%%%

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
