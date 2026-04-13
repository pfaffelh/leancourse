import VersoManual
import Manual.Meta
import Leancourse.Misc.Defs
import Mathlib

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open MyDef

set_option pp.rawOnError true

#doc (Manual) "Notes on Lean" =>
%%%
htmlSplit := .never
tag := "notesonlean"
%%%


# Lean as a programming language
%%%
tag := "functional"
%%%

Lean is a [functional programming language](https://en.wikipedia.org/wiki/Functional_programming) (i.e. it actually only consists of functions). This paradigm is in contrast to [imperative programming](https://en.wikipedia.org/wiki/Imperative_programming)  such as Python, Java and C. Lean comes with many features you might be familiar with, such as a library for output and input, but is still young and many things need to be developed.

# Dependent type theory
%%%
tag := "dependent-type-theory"
%%%

In all programming languages, you have data types such as `int`, `string` and `float`. In Lean, these exist as well, but you can (and will in this course) define own data types. In all cases, we write `x : α` for a term `x` of type `α`, so we write `False : Bool`, `42 : ℕ`, but also `f : ℕ → ℝ` (for a function from ℕ to ℝ, which is an own type) and `0 ≠ 1 : Prop` (the proposition that 0 and 1 are different natural numbers), which is a proposition. Terms and types can depend on variables, e.g. in `∀ (n : ℕ), n < n + 1 : Prop` and `f : (n : ℕ) → (Fin n → ℝ)` (where `Fin n` is the type which carries `{0, ..., n-1}`), which is a function `f` with domain `ℕ` such that `f n ∈ ℝ^n`.

As we see, these new data types are more abstract in the sense that Lean understands `ℕ` (and `ℝ`) as infinite types, which are not limited by floating point arithmetic. E.g., `ℕ` actually represents an infinite set that is characterized by containing `0`, and if it contains `n`, then it also contains the successor of `n` (represented by `succ n`). Accordingly, the real numbers are defined by an equivalence relation on Cauchy sequences, which is quite elaborate. (Although `ℝ` is implemented as such a quotient within `Lean`, we will not have to deal with these implementation details when working with real numbers, since we will rely on results in `Mathlib`, the mathematical library, taking care of these details.)


# Universes, Types and Terms
%%%
tag := "universes"
%%%

In Lean, there are three levels of objects: universes, types and terms. We are concerned here with the last two. Of particular interest is the type `Prop`, which consists of statements that can be `True` or `False`. It includes mathematical statements, so either the hypotheses, or the goal of what is to be proven. A hypothesis in Lean has the form `hP : P`, which means `P` is true, and this statement is called `hP`. Synonomously, it meansthat `P` is true and `hP` is a proof of `P`. The hypotheses here have names `P Q R S`, and the proofs of the hypotheses `hP hQ hR hS`. All names can be arbitrary. Furthermore, there are hypotheses of the form `P → Q`, which is the statement that `P` implies `Q`. (Note the similarity to function notation as in `f : ℝ → ℝ`.)

# Function definitions
%%%
tag := "functions"
%%%

In `Lean`, the function `f : ℕ → ℕ, x ↦ 2x` is defined as
```lean
def f : ℕ → ℕ := fun x ↦ 2*x
```
(Write `\mapsto` for `↦`.) It is assumed that the `x` is only introduced to
define `f`. The application of `f` to an `x : ℕ` is then done using `f x`. (The notation `f x` is an abbreviation for `f(x)`, since `Lean` is sparing with parenthesis.)

## Pattern matching
%%%
tag := "pattern-matching"
%%%

For functions on inductive types (like `ℕ`, `List α`, `Option α`,
`Bool`), the most natural way to define them is by *pattern matching*
on the constructors of the input.  The syntax uses `match ... with`
and one branch per constructor, each prefixed by a `|`.

For example, the factorial function on `ℕ` matches on whether the
input is `0` or a successor `n + 1`:

```lean
def factorial : ℕ → ℕ
  | 0     => 1
  | n + 1 => (n + 1) * factorial n
```

Each branch may use the variables introduced by its pattern (here
`n` on the right-hand side).  Lean checks two things automatically:

1. *Exhaustiveness.*  Every constructor of `ℕ` is covered (the cases
   `0` and `n + 1` exhaust `ℕ`).  If you forget a case, Lean
   complains.
2. *Termination.*  The recursive call `factorial n` is on a strictly
   smaller argument than `n + 1`, so the definition is well-founded.

Pattern matching works for any inductive type:

```lean
-- A function on Bool
def negate : Bool → Bool
  | true  => false
  | false => true

-- A function on Option α: extract or use a default
def Option.getD' {α : Type*} (d : α) : Option α → α
  | none   => d
  | some a => a

-- A recursive function on List α
def length' {α : Type*} : List α → ℕ
  | []      => 0
  | _ :: xs => 1 + length' xs
```

The same syntax can be used inline with `match`:

```lean
example (n : ℕ) : ℕ :=
  match n with
  | 0     => 42
  | _ + 1 => 0
```

You will see pattern matching extensively in the Functional
Programming chapter, where we use it to define data structures and
recursive algorithms.

# Equality
%%%
tag := "equality"
%%%

Due to the multitude of types in Lean, we have to be careful about equality. In Lean, there are three types of equality:

* Syntactic equality: If two terms are letter-for-letter equal, then they are syntactically equal. However, there are a few more situations in which two terms are syntactically equal. Namely, if one term is just an abbreviation for the other (for example, `x = y` is an abbreviation for ` Eq x y`, where `Eq` is a function which takes two terms of the same type, and assigns `True` if they are the same and `False` otherwise), then these both terms are syntactically equal. Also equal are terms in which globally quantified variables have different letters. For example, `∀ x, ∃ y, f x y` and `∀ y, ∃ x, f y x` are syntactically equal.

* Definitional equality: Some terms are equal by definition in Lean. For example, `x : ℕ`, `x + 0` is by definition identical to `x`. However, `0 + x` is not   definitionally identical to `x`. This is apparently only due to the     internal definition of addition of natural numbers in Lean.

* Propositional equality: If there is a proof of `x = y`, then `x` and `y` are said to be propositionally equal. Similarly, terms `P` and `Q` are said to be propositionally equal if you can prove `P ↔ Q`. Some Lean tactics only work up to syntactic equality (such as `rw`), others (most) work up to definitional equality (such as `apply`, `exact`,...) This means that the tactic automatically transforms terms if they are syntactically or definitional equality.

There is a special kind of equality to be observed with sets and functions. For example, two functions are exactly the same if they return the same value for all values in the domain. This behavior is called *extensionality* in the theory of programming languages. (If extensionality applies, then, for example, two sorting algorithms are the same if they always produce the same result).

# Different parentheses in `Lean`
%%%
tag := "parenthesis"
%%%

There are (essentially) three different types of parentheses in `Lean` statements. The simplest is `(...)`, which, as in normal use, indicates parentheses in the sense of what belongs together. However, you have to learn how `Lean` brackets internally when no '()' are given. Operators like *and* (`∧`), *or* (`∨`), are right-associative, so e.g. `P ∧ Q ∧ R := P ∧ (Q ∧ R)`. The application of functions in sequence, such as `f : ℕ → ℝ` and `g : ℝ → ℝ `, applied to `n : ℕ` is `g (f n)`, because `g` expects an input of type `ℝ`, and this is what `f n` provides. You cannot omit (...), i.e. in this case the parenthesis is left-associative.

Now let's comment on the parentheses `[...]` and `{...}`. For example, `#check@ gt_iff_lt` (the statement that `a>b` holds if and only if `b<a` holds), where both types occur. This yields
```
gt_iff_lt : ∀ {α : Type u_1} [_inst_1 : has_lt α] {a b : α}, a > b ↔ b < a
```

When this result is applied, the statements in `{...}` and `[...]` are added by `Lean` itself. The statements in `{...}` depend on the type of the objects that have to be given, and can therefore be inferred. (Above, when applying `gt_iff_lt`, the variables `a` and `b` have to be given.) Therefore, their type is also known, and one does not have to `α` is not explicitly specified. Since the application is made to a concrete `α` (for example, `ℕ`), and `Lean` knows a lot about the natural numbers, the type class system can look up many properties of `ℕ`, and also finds that `has_lt ℕ` holds (i.e. on `ℕ` at least a partial order is defined).

# Proving propositions and evaluating functions
%%%
tag := "term"
%%%

Although we almost exclusively prove propositions in `tactic` mode in these notes, it is instructive to know about the simplest example of how to turn the proof to `term` mode: There are two rules:

* The tactic `exact` is the same as calling a function.
* The tactic `intro` is like taking a variable, which will be the argument of a function which is evaluated in the next step.

Let us consider two examples:

The `term` proof
```lean
example (P : Prop) : False → P := False.elim
```
is the same as
```lean
example (P : Prop) : False → P := by
    exact False.elim
```

The `term` proof
```lean
example (s t : Set ℝ) (hst : s ⊆ t) (x : ℝ) :
    x ∈ s → x ∈ t := fun hx ↦ hst hx
```
is the same as
```lean
example (s t : Set ℝ) (hst : s ⊆ t) (x : ℝ) :
    x ∈ s → x ∈ t := by
    intro hx
    exact hst hx
```

# Exploring definitions with `#check`, `#print` and `inferInstance`
%%%
tag := "checkprint"
%%%

Lean provides a handful of *commands* that are invaluable for exploring
a library like Mathlib.  They all start with `#` and only print
information -- they do not contribute to a proof.

- `#check e` prints the type of the term or expression `e`.  This is
  the fastest way to learn what a lemma says, or what type a definition
  has.
- `#check @lemma` (with a leading `@`) prints the type of the lemma
  *without* hiding implicit and instance arguments.  Use `@` when you
  want to see every argument.
- `#print name` prints the *definition* of the constant `name`.  For a
  typeclass, this shows you the list of fields; for a `def`, the body;
  for a `structure`, the constructor and fields.
- `#eval e` evaluates the term `e` (when it is computable) and prints
  the result.  It works on concrete `ℕ`, `List`, etc., but not on
  abstract propositions.

A very common idiom is to ask Lean whether a given type has a specific
instance (e.g. "is `ℕ` a commutative monoid?"):

```lean
-- "Does ℕ have an AddCommMonoid instance?" -- yes.
#check (inferInstance : AddCommMonoid ℕ)
```

The term `inferInstance` asks Lean to synthesize an instance of the
indicated type; if no such instance exists the command will fail with
a readable error message.

Two tactics complement these commands during an interactive proof:

- `exact?` searches Mathlib for a single lemma that closes the current
  goal and prints a `exact <lemma>` line you can copy.
- `apply?` is the same, but it suggests lemmas whose *conclusion*
  matches the goal, leaving side conditions as new subgoals.

Together, `#check`, `#print`, `inferInstance`, `exact?` and `apply?`
are the main tools for navigating an unfamiliar part of Mathlib.

# Two abbreviations
%%%
tag := "abreviation"
%%%

There are at least two abbreviations used in `Mathlib` which you will encounter frequently.

If you have `h : x = y` and `hx : P x` (with `P x : Prop`), you can prove `P y` by replacing `h` in `hx`. The shorthand notation for this is `h ▸ hx`. (Write `\t` for `▸`).

```lean
example (P : ℕ → Prop) (x y : ℕ) (h : x = y) (hx : P x) :
    P y := by
  exact h ▸ hx
```

Sometimes, bracketing is critical, and it appears frequently that it has the form
`apply first (second very long statement)`, and you might get lost since the closing brackets are far away from their opening counterparts. In this case, we write `apply first <| second very long statement`, which does not need a closing symbol.

```lean
example (P Q : Prop) (hP : P) (hnP : ¬P) : Q := by
    apply False.elim <| hnP hP
```

# Defining new notation
%%%
tag := "notation"
%%%

Lean allows you to define custom notation using the `notation` command. This is useful when you want a concise mathematical symbol for a frequently used expression. The general syntax is
```
notation "symbol" arg1 arg2 ... => expression
```
where the left-hand side describes the syntax pattern (with arguments) and the right-hand side is the Lean expression it expands to. Here is a simple example:

```lean
section NotationDemo

notation "δ" => (2 : ℕ)
#check (δ : ℕ)

```

After this definition, `δ` is replaced by `2` everywhere. The notation is purely syntactic: Lean replaces every occurrence of the new notation by the right-hand side before type checking. Here is a more interesting example with an argument:

```lean
notation "double" x => x + x
#eval double 5 -- 10

end NotationDemo
```

You can also define infix notation with a priority (determining how tightly the operator binds):

```lean
section InfixDemo

infixl:65 " ⊕⊕ " => fun (a b : ℕ) => a + b + 1
#eval 3 ⊕⊕ 4 -- 8

end InfixDemo
```

Here, `infixl` means left-associative infix, `65` is the binding power (the same as `+`), and the spaces around `⊕⊕` are part of the syntax. Similarly, `infixr` gives right-associative infix, and `prefix` / `postfix` are available for unary operators.

For more complex notation involving multiple tokens, you can use the `syntax` and `macro_rules` commands, but `notation` and the infix variants cover most common use cases.

# The `abbrev` command
%%%
tag := "abbrev"
%%%

The `abbrev` command introduces a definition that is *reducibly transparent*, meaning Lean's elaborator will unfold it automatically whenever needed. In contrast, a definition introduced with `def` is *semireducible* and will not be unfolded automatically.

```lean
abbrev MyNat := ℕ
```

After this, `MyNat` and `ℕ` are interchangeable everywhere — Lean treats them as definitionally equal without needing any extra work. In particular, all type class instances that apply to `ℕ` are automatically available for `MyNat`. Compare this with

```lean
def MyNat' := ℕ
```

where `MyNat'` is a genuinely new type: Lean will *not* automatically apply `ℕ` instances to `MyNat'`, and you would have to derive or register them yourself.

Use `abbrev` when you want a short name for a type or expression but do not want to create a new abstraction barrier. Use `def` when you intentionally want to hide the definition (e.g. to prevent the simplifier from unfolding it).
