import VersoManual
import Manual.Meta
import Leancourse.Misc.Defs
import Mathlib

open Verso.Genre Manual

set_option pp.rawOnError true

#doc (Manual) "Notes on Lean" =>
%%%
htmlSplit := .never
tag := "lean"
%%%


# Lean as a programming language
%%%
tag := "functional"
%%%

Lean is a functional programming language (i.e. it actually only consists of functions). This paradigm is in contrast to procedural programming languages such as Python, Java and C. It comes with many features such as libraries for output and input, but is still young and many things need to be developed.

# Dependent type theory
%%%
tag := "dependent-type-theory"
%%%

In all programming languages, you have data types such as int, string, float. In Lean, these exist as well, but you can (and will in this course) define own data types. In all cases, we write `x : α` for a term `x` of type `α`, so we write `False : Bool`, but also `f : ℕ → ℝ` (a function from ℕ to ℝ) and `0 ≠ 1 : Prop` (the proposition that 0 and 1 are different numbers in ℕ), which is a proposition. Terms and types can depend on variables, e.g. in `∀ (n : ℕ), n < n + 1 : Prop` and `f : (n : ℕ) → (Fin n → ℝ)` (where `Fin n` is the type which carries `{0, ..., n-1}`), which is a function `f` with domain `ℕ` such that `f n ∈ ℝ^n`.

As we see, these new data types are more abstract in the sense that Lean is understand `ℕ` (and `ℝ`) as infinite types, which are not limited by floating point arithmetic.
E.g., `ℕ` actually represents an infinite set that is characterized by containing `0`, and if it contains `n`, then it also contains the successor of `n` (represented by `succ n`). Accordingly, the real numbers are defined by an equivalence relation on Cauchy sequences,  which is quite elaborate.

Regarding the notation: for sets, we are used to writing `n ∈ ℕ` if `n` is a natural number. In type theory, we write `n : ℕ` and say that `n` is a term (or expression) of type `ℕ`. More generally, when typing an expression, Lean checks its type and tells us if it can make sense of our statement. (Incidentally, this can be quite confusing: for example, the statement `(x : ℕ) → (x : ℤ)`, i.e. (every natural number is also an integer) is not at all comprehensible for `lean`. Because `x` is a term of type `ℕ` (and thus of no other type), so that `x : ℤ` makes no sense at all for Lean. In this case, the solution is an 'invisible mapping' (or coercion) `coe : ℕ → ℤ`.)

# Universes, Types and Terms
%%%
tag := "universes"
%%%

In Lean, there are three levels of objects: universes, types and terms. We are concerned here with the last two. Of particular interest is the type `Prop`, which consists of statements that can be true or false . It includes mathematical statements, so either the hypotheses, or the goal of what is to be proven. A hypothesis in Lean has the form `hP : P`, which means `P` is true, and this statement is called `hP`. It can also mean that `P` is true and `hP` is a proof of `P`. The hypotheses here have names `P Q R S`, and the names of the hypotheses `hP hQ hR hS`. All names can be arbitrary. Furthermore, there are hypotheses of the form `P → Q`, which is the statement that `P` implies `Q`. (Note the similarity to function notation as in `f : ℝ → ℝ`.)

# Function definitions
%%%
tag := "functions"
%%%

In `Lean`, for example, the function `f : ℕ → ℕ, x ↦ 2x` is defined as
```lean
def f : ℕ → ℕ := fun x ↦ 2*x
```
(Write `\mapsto` for `↦`.) It is assumed that the `x` is only introduced to
define `f`. The application of `f` to an `x : ℕ` is then done using `f x`. (The notation `f x` is an abbreviation for `f(x)`, since `Lean` is sparing with parenthesis.)

# Equality
%%%
tag := "equality"
%%%

Due to the multitude of types in Lean, we have to be careful about equality. In Lean, there are three types of equality:

* Syntactic equality: If two terms are letter-for-letter equal, then they are syntactically equal. However, there are a few more situations in which two terms are syntactically equal. Namely, if one term is just an abbreviation for the other (for example, `x = y` is an abbreviation for ` Eq x y`, where `Eq` is a function which takes two terms of the same type, and assigns `True` if they are the same and `False` otherwise), then these both terms are syntactically equal. Also equal are terms in which globally quantified variables have different letters. For example, `∀ x, ∃ y, f x y` and `∀ y, ∃ x, f y x` are syntactically equal.

* Definitional equality: Some terms are by definition equal in Lean. For `x : ℕ`, `x + 0` is by definition identical to `x`. However, `0 + x` is not   definitionally identical to `x`. This is apparently only due to the     internal definition of addition of natural numbers in Lean.

* Propositional equality: If there is a proof of `x = y`, then `x` and `y` are said to be propositionally equal. Similarly, terms `P` and `Q` are said to be propositionally equal if you can prove `P ↔ Q`. Some Lean Tactics only work up to syntactic equality (such as `rw`), others (most) work up to definitional equality (such as `apply`, `exact`,...) This means that the tactic automatically transforms terms if they are syntactically or definitional equality. There is a special kind of equality to be observed with sets and functions. For example, two functions are exactly the same if they return the same value for all values in the domain. This behavior is called *extensionality* in the theory of programming languages. (If extensionality applies, then, for example, two sorting algorithms are the same if they always produce the same result).

# Different parentheses in `Lean`
%%%
tag := "parenthesis"
%%%

There are (essentially) three different types of parentheses in `Lean` statements. The simplest is `(...)`, which, as in normal use, indicates parentheses in the sense of what belongs together. However, you have to learn how 'Lean' brackets internally when no '()' are given. Operators like *and* (`∧`), *or* (`∨`), are right-associative, so e.g. `P ∧ Q ∧ R := P ∧ (Q ∧ R)`. The application of functions in sequence, such as `f : ℕ → ℝ` and `g : ℝ → ℝ `, applied to `n : ℕ` is `g (f n)`, because `g` expects an input of type `ℝ`, and this is what `f n` provides. You cannot omit (...), i.e. in this case the parenthesis is left-associative.

Now let's comment on the parentheses `[...]` and `{...}`. For example, `#check@ gt_iff_lt` (the statement that `a>b` holds if and only if `b<a` holds), where both types occur. This yields
```
gt_iff_lt : ∀ {α : Type u_1} [_inst_1 : has_lt α] {a b : α}, a > b ↔ b < a
```

When this result is applied, the statements in `{...}` and `[...]` are added by `Lean` itself. The statements in `{...}` depend on the type of the objects that have to be given, and can therefore be inferred. (Above, when applying `gt_iff_lt`, the variables `a` and `b` have to be given.) Therefore, their type is also known, and one does not have to `α` is not explicitly specified. Since the application is made to a concrete `α` (for example, `ℕ`), and `Lean` knows a lot about the natural numbers, the type class system can look up many properties of `ℕ`, and also finds that `has_lt ℕ` holds (i.e. on `ℕ` at least a partial order is defined).
