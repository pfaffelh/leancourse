import VersoManual
import Manual.Meta
import Leancourse.Markup
import Leancourse.Coursenotes.References
import Mathlib

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open Leancourse.Refs
open MyDef

set_option pp.rawOnError true

#doc (Manual) "Types and terms I: functions and inductive types" =>
%%%
htmlSplit := .never
tag := "types"
%%%

Lean has the data types every programming language has — `int`, `string`, `float` — and you can define your own, as you will in this course. Throughout, `x : α` means that `x` is a term of type `α`: `false : Bool`, `42 : ℕ`, `f : ℕ → ℝ` for a function from ℕ to ℝ (itself a type), and `0 ≠ 1 : Prop` for the proposition that 0 and 1 differ. Terms and types can depend on variables, e.g. in `∀ (n : ℕ), n < n + 1 : Prop` (the term `n < n + 1` depends on `n : ℕ`) and `f : (n : ℕ) → (Fin n → ℝ)` where `Fin n` is the type which carries `{0, ..., n-1}` (here, the type `Fin n → ℝ` depends on `n : ℕ`), which is a function `f` with domain `ℕ` such that `f n ∈ ℝ^n`.

Two words for terms recur throughout, depending on their type: a term `h : P` whose type `P` is a `Prop` is called a *proof* (of `P`), while a term `a : α` whose type `α` is a `Type u` (where `u` is a *universe level*, see {ref "type-universes"}[The universe hierarchy] below) is called *data*. So `42 : ℕ` and `true : Bool` are data, whereas any term of the proposition `0 ≠ 1` is a proof of it.

These data types are abstract: Lean treats `ℕ` as genuinely infinite, not as a machine integer of fixed width. `ℕ` is the `zero`/`succ` construction of the {ref "nat"}[previous chapter].

In Lean every object is a term, and every term has a type. A type is itself a term, so it has a type as well.

Types and terms cannot be treated separately: a type is known once we know how its terms are built and how they are used. This chapter and the next therefore describe every way of forming a type in the same four steps.

:::table (align := left) +header
* + step
  + question
  + for functions
* + Formation
  + How is the type written?
  + `α → β`
* + Construction
  + How is a term of the type built?
  + `fun x => e`
* + Use
  + How is a term of the type used?
  + `f a`
* + Computation
  + What happens when a term that was just built is used?
  + `(fun x => e) a` reduces to `e` with `a` for `x`
:::

The four steps are the four kinds of rule of Lean's type theory, stated formally in {ref "rules"}[chapter 1.4]. This chapter treats universes, function types and inductive types; the {ref "type-formers"}[next chapter] structures, pairs, subtypes, type families and quotients. In several of these types the type of one part depends on the value of another. Such types are called *dependent*, and they are what separates Lean from most programming languages.

The [slides](slides/1-2-types/) for this chapter follow it section by section.

# Commands for terms
%%%
tag := "naming-terms"
%%%

Four commands recur in every chapter.

* `#check t` prints the type of the term `t`.
* `def name : T := t` gives the name `name` to the term `t`, after checking that `t` has type `T`. `theorem` does the same for proofs.
* `example : T := t` checks that `t` has type `T`, without giving it a name.
* `#eval t` computes the value of `t` and prints it. It runs compiled code; `rfl` instead asks the kernel to reduce ({ref "defeq"}[Definitional equality]), and for the definitions of this chapter both give the same value.

```lean
#check 2 + 2           -- 2 + 2 : ℕ
def four : ℕ := 2 + 2
example : four = 4 := rfl
#eval four             -- 4
```

The text after `--` is a comment; in the examples it shows what Lean prints.

# The universe hierarchy
%%%
tag := "type-universes"
%%%

Every type is itself a term, so it has a type as well. These types of types are called *universes*. They form a countably infinite tower, which is what keeps the system consistent.

At the bottom sit the two universes you meet first:

```lean
#check (42 : ℕ)         -- a term ...
#check (ℕ : Type)       -- ... whose type ℕ lives in `Type`
#check ((2 = 2) : Prop) -- a proposition ...
#check (Prop : Type)    -- ... and `Prop` lives in `Type`
```

`Type`, the same as `Type 0`, is the universe of ordinary data types (`ℕ`, `ℝ`, `Bool`, `List α`, ...). `Prop` is the universe of *propositions*, statements that are true or false. `Type` cannot contain itself, so it lives in a larger universe `Type 1`, which lives in `Type 2`, and so on without end:

```lean
#check (Type 0 : Type 1)    -- `Type 0` is `Type`
#check (Type 1 : Type 2)    -- Type 1 : Type 2
```

The whole tower is captured by a single keyword `Sort`:

* `Sort 0` is `Prop`;
* `Sort 1` is `Type 0`, i.e. `Type`;
* `Sort (u+1)` is `Type u`.

```lean
example : Sort 0 = Prop := rfl
example : Sort 1 = Type := rfl
example : Type = Type 0 := rfl
```

So `Sort` covers `Prop` and all the `Type u`, and the one rule governing the hierarchy is `Sort u : Sort (u+1)`. Of the four steps, universes have only the first: `Sort u` is a type, and its terms are the types built in the rest of this chapter and the next.

There is deliberately no `Type : Type`. A universe that contains itself admits a version of Russell's paradox for types, *Girard's paradox*, and with it a proof of `False`.

# Function types and Π-types
%%%
tag := "pi-types"
%%%

A function from `ℕ` to `ℕ` is a term of the type `ℕ → ℕ`. In Lean the type of the value may depend on the argument; the function type is then called a *dependent function type*, or *Π-type*.

*Formation.* For types `α` and `β`, `α → β` is the type of functions from `α` to `β`. More generally, if `β x` is a type for every `x : α`, then `(x : α) → β x` is the type of functions `f` with `f x : β x` for every `x`.

*Construction.* A function is built with `fun`. If `e` is a term of type `β x`, in which `x` may occur, then `fun x => e` has type `(x : α) → β x`. Mathematics writes `x ↦ x^2`; Lean writes `fun x => x ^ 2`, or `fun x ↦ x ^ 2` with the arrow `↦` (typed `\mapsto`).

*Use.* A function is applied by writing it in front of its argument: `f a`, without parentheses, has type `β a`.

*Computation.* Applying a function built with `fun` substitutes the argument: `(fun x => e) a` reduces to `e` with `a` in place of `x`. This is the β-rule of {ref "reduction-rules"}[the reduction rules].

```lean
#check (fun n => n + 1 : ℕ → ℕ)
#eval (fun n : ℕ => n + 1) 4        -- 5
example : (fun n : ℕ => n + 1) 4 = 5 := rfl
```

## Defining functions
%%%
tag := "pure-functions"
%%%

A function is usually given a name with `def`, writing its arguments before the `:=`:

```
def name (arguments) : resultType := body
```

This is short for `def name : (arguments) → resultType := fun arguments => body`. So the following defines `double`, taking one argument `n : ℕ` and returning `2 * n`:

```lean
def double (n : ℕ) : ℕ := 2 * n

#eval double 5    -- 10
example : double = fun n => 2 * n := rfl
```

A *pure function* returns the same result for the same arguments, exactly as in mathematics. Functions of several arguments are *curried*: a function of two arguments is a function that takes one argument and returns another function.

```lean
def add (a b : ℕ) : ℕ := a + b

#eval add 3 4    -- 7
#check add 3     -- add 3 : ℕ → ℕ
```

The type of `add` is `ℕ → ℕ → ℕ`, which reads as `ℕ → (ℕ → ℕ)`; so `add 3` is itself a function of type `ℕ → ℕ`.

## Anonymous functions
%%%
tag := "anonymous-functions"
%%%

A function built with `fun` needs no name; it can be applied on the spot:

```lean
#eval (fun x : ℕ ↦ x + 1) 5       -- 6
#eval (fun x y : ℕ ↦ x * y) 3 4   -- 12
```

Shorter still is the `·` placeholder (a centered dot, typed `\cdot`), which stands for an anonymous argument: `(· + 10)` is shorthand for `fun x ↦ x + 10`, and several `·` become successive arguments, so `(· + ·)` means `fun x y ↦ x + y`.

## Dependent functions

A proof of `∀ n : ℕ, n < n + 1` takes each `n : ℕ` to a proof of `n < n + 1`. It is a function as well, of the same kind as `fun n => n + 1`; the only difference is that the type of the value, `n < n + 1`, depends on `n`.

There are two notations for the Π-type. We write `(x : α) → β x`, or `α → β` if `β` does not mention `x`, when `β x` is data, and `∀ x : α, β x` when `β x` is a proposition. The two notations denote the same type, so `rfl` proves them equal:

```lean
example : ∀ n : ℕ, n < n + 1 :=
  fun n => Nat.lt_succ_self n

example : ((n : ℕ) → n < n + 1) =
    (∀ n : ℕ, n < n + 1) := rfl
```

A dependent function whose values are data: `Fin n` is the type of the natural numbers less than `n`, and `Fin.last n` is the largest element of `Fin (n + 1)`. So each value of `lastOf` lies in a different type.

```lean
def lastOf : (n : ℕ) → Fin (n + 1) :=
  fun n => Fin.last n

#check lastOf 3   -- lastOf 3 : Fin (3 + 1)
#eval lastOf 3    -- 3
```

In terms of sets, a function `f : (x : α) → β x` chooses one element `f x ∈ β x` for every `x`. It is an element of the product $`\prod_{x \in \alpha} \beta(x)`. This is where the name Π comes from.

## Polymorphic functions
%%%
tag := "polymorphic-functions"
%%%

The argument of a function may itself be a type. The identity function takes a type `α` and returns the identity on `α`; its type `(α : Type) → α → α` is a Π-type, because the type of the rest depends on `α`:

```lean
def myId (α : Type) (a : α) : α := a

#check myId ℕ 42          -- myId ℕ 42 : ℕ
#check myId String "hi"   -- myId String "hi" : String
```

Usually you do not want to pass the type explicitly every time, so you make it an *implicit* argument with braces `{...}`; Lean then infers it from the other arguments. The prefix `@` makes the implicit arguments explicit again, for instance to see them in `#check`:

```lean
def myId' {α : Type} (a : α) : α := a

#check myId' 42           -- myId' 42 : ℕ
#check @myId'             -- {α : Type} → α → α
```

A definition that should work in *every* universe takes a universe variable. You may introduce one with the `universe` command, or, most commonly, write `Type*`, which inserts a fresh universe variable for you:

```lean
universe u
def idOne (α : Type u) (a : α) : α := a

def idStar {α : Type*} (a : α) : α := a
```

This is why signatures throughout Mathlib read `{α : Type*}`: the same definition then applies whether `α` is small like `ℕ` or large like `Type` itself.

## Proofs as arguments

An argument may also be a proof. A division that demands a proof that the denominator is not zero cannot be called with zero:

```lean
def safeDiv (a b : ℤ) (_ : b ≠ 0) : ℤ := a / b

#eval safeDiv 10 3 (by simp)   -- 3
```

The third argument is a proof of `3 ≠ 0`, here written as a tactic proof `by simp` in the place of a term. The type `(a b : ℤ) → b ≠ 0 → ℤ` of `safeDiv` is a Π-type, because the type of the proof depends on `b`.

# Inductive types
%%%
tag := "inductive"
%%%

`Nat`, `List`, `Option`, `Bool` and `Empty` are all *inductive* types; `Nat` and `Bool` were dissected in the {ref "nat-intro"}[previous chapter]. An inductive type is given by a list of *constructors*, each saying how to build a new element out of existing pieces. Declaring the natural numbers by hand reproduces exactly the structure of `Nat`:

```lean
inductive MyNat where
  | zero : MyNat
  | succ (n : MyNat) : MyNat
```

*Formation.* The declaration introduces the type `MyNat : Type`. The universe of an inductive type must be large enough to hold the arguments of all its constructors.

*Construction.* The terms of `MyNat` are built with the two constructors `MyNat.zero` and `MyNat.succ`, and every element is either `zero` or `succ n`. Where Lean already knows that a `MyNat` is expected, the type name can be dropped and a leading dot written instead: `.succ .zero` for `MyNat.succ MyNat.zero`.

*Use.* A term of an inductive type is used by distinguishing which constructor built it: *pattern matching*, below. Lean translates every pattern match into the type's *recursor* `MyNat.rec`, which the declaration also introduces.

*Computation.* Applied to a term built by a constructor, a pattern match takes the branch for that constructor. For the recursor this is the ι-rule of {ref "reduction-rules"}[the reduction rules], `MyNat.rec z s (.succ n) ⟶ s n (MyNat.rec z s n)`, the firing we watched for `Nat`.

```lean
#check (MyNat.succ MyNat.zero : MyNat)
example : MyNat := .succ (.succ .zero)
```

Inductive types also cover non-recursive data:

```lean
inductive Colour where
  | red | green | blue

example : Colour := .green
```

and types with a parameter:

```lean
-- `MyOption α` is `none` or `some a` with `a : α`
inductive MyOption (α : Type) where
  | none : MyOption α
  | some (a : α) : MyOption α

example : MyOption ℕ := .some 3
```

Here `MyOption α` is a type for every type `α`. Inductive types are the main mechanism by which new data types enter Lean, and `Mathlib` uses them throughout.

## Pattern matching
%%%
tag := "pattern-matching"
%%%

A function on an inductive type is defined by *pattern matching* on the constructors of its argument: one branch per constructor, each prefixed by `|`. The function `myNot` on `Bool` in the {ref "bool"}[previous chapter] was of this kind. The factorial function on `ℕ` matches on whether the input is `0` or a successor `n + 1`:

```lean
def factorial : ℕ → ℕ
  | 0     => 1
  | n + 1 => (n + 1) * factorial n
```

Each branch may use the variables introduced by its pattern (here `n` on the right-hand side). Lean checks two things automatically:

1. *Exhaustiveness.* Every constructor of `ℕ` is covered (the cases `0` and `n + 1` exhaust `ℕ`). If you forget a case, Lean complains.
2. *Termination.* The recursive call `factorial n` is on a strictly smaller argument than `n + 1`, so the recursion ends.

It works just as well for the inductive types you declare yourself. For `MyNat`, doubling and the conversion to `ℕ` are defined by matching on the two constructors:

```lean
def MyNat.double : MyNat → MyNat
  | .zero   => .zero
  | .succ n => .succ (.succ (MyNat.double n))

def MyNat.toNat : MyNat → ℕ
  | .zero   => 0
  | .succ n => MyNat.toNat n + 1

#eval (MyNat.double (.succ .zero)).toNat   -- 2
```

Writing plain `zero` in place of `.zero` would fail: there is no `zero` in scope, only `MyNat.zero`. A name such as `MyNat.toNat`, which begins with the name of a type, can also be written after a term of that type, separated by a dot: for `m : MyNat`, `m.toNat` means `MyNat.toNat m`.

Pattern matching works for any inductive type. A list `List α` has two constructors: the empty list `[]`, and `a :: l`, the list with first element `a` followed by the list `l`. The pattern `_` matches anything and names nothing.

```lean
-- A function on Option α: extract or use a default
def Option.getD' {α : Type*} (d : α) : Option α → α
  | none   => d
  | some a => a

-- A recursive function on List α
def length' {α : Type*} : List α → ℕ
  | []      => 0
  | _ :: xs => 1 + length' xs
```

The same syntax can be used inside a term with `match`:

```lean
example (n : ℕ) : ℕ :=
  match n with
  | 0     => 42
  | _ + 1 => 0
```

## Recursion and termination
%%%
tag := "recursion"
%%%

The definitions above are *recursive*: they call themselves on smaller inputs. A classic example with two base cases is the Fibonacci sequence:

```lean
def fib : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | n + 2 => fib n + fib (n + 1)

#eval fib 10    -- 55
```

Lean only accepts a recursive definition once it is convinced the recursion *terminates*. For *structural* recursion, where each call is on a part of the input, as in `factorial`, `length'` and `fib`, this is automatic.

When the recursive call is not on a part of the input, termination is justified by a *measure* that strictly decreases: `termination_by` names the measure, `decreasing_by` proves that it goes down. Euclid's algorithm recurses on `n % m`, the remainder of `n` divided by `m`, which is not a part of `m`, but the first argument strictly decreases. The definition uses a *dependent* `if`: in `if h : c then a else b`, the proof `h : c` is available in `a`, and a proof of `¬c` in `b`.

```lean
def euclidGcd (m n : Nat) : Nat :=
  if _h : m = 0 then n
  else euclidGcd (n % m) m
termination_by m
decreasing_by
  exact Nat.mod_lt n (Nat.pos_of_ne_zero _h)

#eval euclidGcd 48 36   -- 12
```

`termination_by m` declares the measure (the first argument); for the recursive call Lean then asks you to show that it shrinks, i.e. `n % m < m`, which is the goal that `decreasing_by` proves (`Nat.mod_lt`, from `m ≠ 0`). When the decrease is routine, `decreasing_by` can often close it with `omega`, a tactic that proves linear inequalities over `ℕ` and `ℤ`:

```lean
def log2 (n : Nat) : Nat :=
  if _h : 2 ≤ n then 1 + log2 (n / 2) else 0
termination_by n
decreasing_by omega

#eval log2 16   -- 4
```

Lean translates such a definition into *well-founded recursion* (`WellFounded.fix`). The theory behind it, what makes a relation well-founded and why `<` on `Nat` qualifies, is developed in the *Mathematics* part. If `decreasing_by` is left out, Lean tries a standard tactic, `decreasing_tactic`, which handles the simple cases on its own.

## Proving things about recursive definitions
%%%
tag := "recursive-proofs"
%%%

A structurally recursive definition is translated into the recursor, and the recursor computes by ι. So `rfl` and `#eval` see through it, even with a variable in the argument:

```lean
example : fib 10 = 55 := rfl
example (n : ℕ) : fib (n + 2) = fib n + fib (n + 1) := rfl
```

A definition by well-founded recursion does not compute in this way. `#eval` runs it, but the kernel does not unfold `WellFounded.fix`, so `rfl` and `decide` fail even on closed terms:

```lean +error
example : log2 16 = 4 := rfl
```

Instead Lean proves an *equation lemma* for every definition, here `log2.eq_1`, which states the defining equation. Proofs use it through `rw [log2]`, `unfold log2` or `simp [log2]`:

```lean
#check log2.eq_1
-- log2.eq_1 (n : ℕ) : log2 n =
--   if _h : 2 ≤ n then 1 + log2 (n / 2) else 0

example : log2 16 = 4 := by simp [log2]

example (n : ℕ) (h : 2 ≤ n) :
    log2 n = 1 + log2 (n / 2) := by
  rw [log2]
  simp [h]
```

Proofs by induction that follow the recursion of a function, one case per branch, are done with `fun_induction` ({ref "induction"}[induction]).

## The recursor

The {ref "nat-intro"}[previous chapter] used the recursor `Nat.rec` in a *non-dependent* form, into a fixed result type. The true `MyNat.rec` lets that type *depend* on the value being consumed, a dependency recorded by a *motive* `MyNat → Sort u`. With universes and implicit arguments in hand, its full type can be read:

```lean
#check @MyNat.rec
-- {motive : MyNat → Sort u} →
--   motive .zero →                      -- zero case
--   ((n : MyNat) → motive n →
--      motive n.succ) →                 -- succ case
--   (t : MyNat) → motive t
```

With a data-valued `motive` this is *recursion*; with a `Prop`-valued one it is the *induction principle*. Recursion and induction are two readings of the single primitive `MyNat.rec`, which is why the `induction` tactic and recursive definitions feel so alike. The `induction` tactic applies the recursor for you: one subgoal per constructor, with an induction hypothesis for each recursive argument.

## Strict positivity

Not every `inductive` declaration is accepted. A constructor may mention the type being defined, but only *positively*. The *arrow* here is the `→` of a function type: in `α → β` the type `α` of the inputs stands to the left of the arrow, the type `β` of the values to the right. Strictly positive means that in the type of an argument of a constructor, the type being defined never stands to the left of an arrow. The type of the constructor itself does not count: every constructor of a type `T` ends in `→ T`, and only the arguments before that last arrow are checked. An *infinitely-branching* tree, where a `node` carries one subtree for each natural number, is fine, because the argument of `node` has type `ℕ → MyTree`, and there `MyTree` stands to the *right* of `→`:

```lean
inductive MyTree where
  | leaf : ℕ → MyTree              -- a leaf holds a value
  | node : (ℕ → MyTree) → MyTree   -- positive occurrence

-- leaves now carry data, and trees can be built:
example : MyTree := .leaf 7
example : MyTree := .node (fun n => .leaf n)
```

The `leaf` case is what gets the type off the ground. Positivity constrains only *where* `MyTree` may occur, not whether the type has any elements: drop `leaf`, and the declaration is *still accepted*, but no closed `MyTree` can ever be built — every `node` already demands a whole family `ℕ → MyTree` of subtrees, with nothing to start from, so the type is *empty* (like `Empty`; one can even prove `MyTree → False`). With `leaf` present you build upward — `leaf 7`, then `node (fun n => leaf n)`, then trees over those. Note that `leaf` here *carries* a `ℕ`, so different leaves are genuinely different; a bare `leaf : MyTree` would give a single, featureless leaf, indistinguishable from every other.

Because `node` takes a *function* `ℕ → MyTree`, every node has one child per natural number — it branches *infinitely*. It is not that *every* `MyTree` is infinite: a leaf is finite (`leaf 7` is a complete tree), so only trees that actually use `node` are. The infinite branching comes from the function-typed argument. A finitely-branching tree would be `node : MyTree → MyTree → MyTree`, where `MyTree` occurs directly rather than inside a function, so the right-of-`→` case would not arise.

But a constructor that stores a *function out of* the type is rejected. The argument of `Bad.mk` has type `Bad → False`, and there `Bad` stands to the *left* of `→`:

```
inductive Bad where
  | mk : (Bad → False) → Bad
-- error: (kernel) arg #1 of 'Bad.mk' has a non positive
--        occurrence of the datatypes being declared
```

The rejection is not pedantry: were `Bad` allowed, one could prove `False`. Project the stored function out of a `b : Bad` by pattern matching and apply it to `b` itself,

```
def app : Bad → (Bad → False) | .mk f => f
def neg (b : Bad) : False := app b b
```

so `neg : Bad → False`. Then `Bad.mk neg : Bad`, and `neg (Bad.mk neg) : False` is a closed proof of `False`; it even loops, `neg (Bad.mk neg) ⟶ neg (Bad.mk neg)`. Strict positivity outlaws exactly the negative occurrence that ties this self-applying knot, the same concern that rules out `Type : Type`. (That positivity is also *sufficient* for consistency is a deep metatheorem, not something Lean proves about itself.)

# Some history
%%%
tag := "types-history"
%%%

Types were introduced to stop a contradiction. Russell's set $`R = \{x : x \notin x\}` broke Frege's *Grundgesetze der Arithmetik* in 1902 ({ref "prehistory"}[Introduction]). Russell's repair of 1908 gave every object a type and let a type apply only to objects of lower type, so that `x ∈ x` is not false but not a statement at all. Zermelo's repair of the same year instead restricts which sets exist and leaves `x ∈ x` a formula. Mathematics followed Zermelo; proof assistants follow Russell, because a type checker can decide before any question of truth whether an expression means anything.

Alonzo Church turned the simple theory of types into a calculus in 1940, the simply typed lambda calculus on which *Isabelle/HOL* still rests. Dependent types, in which a type may mention a term, came with de Bruijn's Automath (1967) and Martin-Löf's type theory (1971). Coquand and Huet added impredicative quantification in the Calculus of Constructions (1985), and Paulin-Mohring added inductive types (1990). Lean's type theory is a variant of the result, the {ref "cic"}[Calculus of Inductive Constructions]. Three times the same thing happened: a system let an object be applied to itself, a contradiction followed, and types forbade it. In Lean the ban is visible as `Type 0 : Type 1 : Type 2 : ...`.
