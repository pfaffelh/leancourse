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

#doc (Manual) "Functions, inductive types, structures" =>
%%%
htmlSplit := .never
tag := "types"
%%%

Here are the [slides](slides/1-2-functions-inductive-structures/) for this chapter.

Lean has the data types every programming language has — `int`, `string`, `float` — and you can define your own, as you will in this course. Throughout, `x : α` means that `x` is a term of type `α`, and `def name : α := x` gives the term `x` a name ({ref "naming-terms"}[Commands for terms] below):

```lean
def aBool : Bool := false
def answer : ℕ := 42
def square : ℕ → ℕ := fun n => n * n
def zeroNeOne : Prop := 0 ≠ 1
```

Here `square` is a function from ℕ to ℕ, and `ℕ → ℕ` is itself a type; `zeroNeOne` is the proposition that 0 and 1 differ. Propositions and types can depend on terms:

```lean
-- the proposition n < n + 1 depends on n
def ltSucc : Prop := ∀ n : ℕ, n < n + 1
-- the type of vectors in ℝⁿ depends on n
def RVec (n : ℕ) : Type := Fin n → ℝ
def zeroVec (n : ℕ) : RVec n := fun _ => 0
```

`Fin n` is the type of the natural numbers less than `n`; its definition is in {ref "structures"}[Structures] below. `zeroVec` is a function whose value at `n` lies in the type `RVec n`, which depends on `n`.

Two words for terms recur throughout, depending on their type: a term `h : P` whose type `P` is a `Prop` is called a *proof* (of `P`), while a term `a : α` whose type `α` is a `Type u` (where `u` is a *universe level*, see {ref "type-universes"}[The universe hierarchy] below) is called *data*. So `42 : ℕ` and `true : Bool` are data, whereas any term of the proposition `0 ≠ 1` is a proof of it.

These data types are abstract: Lean treats `ℕ` as genuinely infinite, not as a machine integer of fixed width. `ℕ` is the `zero`/`succ` construction of the {ref "nat"}[previous chapter].

In Lean every object is a term, and every term has a type. A type is itself a term, so it has a type as well.

This chapter describes every way of forming and using a type in the same four steps.

:::table (align := left) +header
* + step
  + question
* + Formation
  + How is the type written?
* + Construction
  + How is a term of the type built?
* + Use
  + How is a term of the type used?
* + Computation
  + What happens when a term that was just built is used?
:::

This chapter treats functions, inductive types and structures. Chapter 1.4 adds pairs and Σ-types `(x : α) × β x`, subtypes `{x : α // P x}`, indexed families and quotients `Quot r`; {ref "four-steps"}[The four steps at a glance] at its end has all type formers in one table.

# Commands for terms
%%%
tag := "naming-terms"
%%%

Six commands recur in every chapter.

Three of them make a term known:

* `def name : T := t` gives the name `name` to the term `t`, after checking that `t` has type `T`.
* `theorem name : P := p` does the same for a proposition `P` and a proof `p` of it. Mathlib also accepts `lemma`, with the same meaning; Lean itself knows only `theorem`.
* `example : T := t` checks that `t` has type `T`, without giving it a name.

Three of them show something about a term:

* `#check t` prints the type of the term `t`.
* `#eval t` computes the value of `t` and prints it. It runs compiled code; `rfl` instead asks the kernel to reduce ({ref "defeq"}[Definitional equality]), and for the definitions of this chapter both give the same value.
* `#print name` prints the definition of `name`.

```lean
def four : ℕ := 2 + 2
theorem four_eq : four = 4 := rfl
example : four = 4 := rfl

#check four      -- four : ℕ
#eval four       -- 4
#print four      -- def four : ℕ := 2 + 2
```

The text after `--` is a comment; in the examples it shows what Lean prints.

Why Lean keeps `theorem` apart from `def` is explained in {ref "prop-special"}[Why `Prop` is special].

For a theorem, `#print` shows the proof as a term, also when tactics found it. The arguments before the colon become `∀` and `→` in the statement and `fun` in the proof:

```lean
theorem swap_of_and (P Q : Prop) (h : P ∧ Q) :
    Q ∧ P := by
  constructor
  · exact h.2
  · exact h.1

#print swap_of_and
-- theorem swap_of_and : ∀ (P Q : Prop), P ∧ Q → Q ∧ P :=
-- fun P Q h => ⟨h.right, h.left⟩
```

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

So `Sort` covers `Prop` and all the `Type u`, and the one rule governing the hierarchy is `Sort u : Sort (u+1)`; in particular `Prop : Type`. In signatures you will often see `{α : Type*}`: `α` is a type in some universe `Type u`, and Lean introduces the universe variable `u` itself ({ref "polymorphic-functions"}[Polymorphic functions] below). Of the four steps, universes have only the first: `Sort u` is a type, and its terms are the types built in the rest of this chapter and in {ref "type-formers"}[chapter 1.4].

There is deliberately no `Type : Type`. A universe that contains itself admits a version of Russell's paradox for types, [*Girard's paradox*](https://en.wikipedia.org/wiki/System_U), and with it a proof of `False`.

# Function types and Π-types
%%%
tag := "pi-types"
%%%

A function from `ℕ` to `ℕ` is a term of the type `ℕ → ℕ`. In Lean the type of the value may depend on the argument; the function type is then called a *dependent function type*, or *Π-type*. The ordinary function type `α → β` is the Π-type `(x : α) → β` whose `β` does not depend on `x`; Lean treats the two as the same type:

```lean
example : (ℕ → ℕ) = ((n : ℕ) → ℕ) := rfl
```

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
number := false
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
number := false
%%%

A function built with `fun` needs no name; it can be applied on the spot:

```lean
#check (fun x : ℕ ↦ x + 1)
-- fun x => x + 1 : ℕ → ℕ
#eval (fun x : ℕ ↦ x + 1) 5       -- 6
#check (fun x y : ℕ ↦ x * y)
-- fun x y => x * y : ℕ → ℕ → ℕ
#eval (fun x y : ℕ ↦ x * y) 3 4   -- 12
```

Shorter still is the `·` placeholder (a centered dot, typed `\cdot`), which stands for an anonymous argument: `(· + 10)` is shorthand for `fun x ↦ x + 10`, and several `·· ` become successive arguments, so `(· + ·)` means `fun x y ↦ x + y`.

## Dependent functions
%%%
number := false
%%%

A proof of `∀ n : ℕ, n < n + 1` takes each `n : ℕ` to a proof of `n < n + 1`. It is a function as well, of the same kind as `fun n => n + 1`; the only difference is that the type of the value, `n < n + 1`, depends on `n`.

There are two notations for the Π-type. We write `(x : α) → β x`, or `α → β` if `β` does not mention `x`, when `β x` is data, and `∀ x : α, β x` when `β x` is a proposition. The two notations denote the same type, so `rfl` proves them equal:

```lean
example : ∀ n : ℕ, n < n + 1 :=
  fun n => Nat.lt_succ_self n

example : ((n : ℕ) → n < n + 1) =
    (∀ n : ℕ, n < n + 1) := rfl
```

The first proof is written down directly as a term. A proof with `by` builds such a term as well ({ref "term"}[Tactic mode and term mode]).

A dependent function whose values are data: Mathlib's `ZMod n` is the type ℤ/nℤ of integers modulo `n` (with `ZMod 0 = ℤ`). The function `sevenMod` takes `n` to the residue class of `7` in ℤ/nℤ. Its definition reads `7` for every `n`, but each value lies in a different type and is a different element there:

```lean
def sevenMod : (n : ℕ) → ZMod n :=
  fun _ => 7

#check sevenMod 5   -- sevenMod 5 : ZMod 5
#eval sevenMod 5    -- 2
#eval sevenMod 0    -- 7
```

The numeral `7` in `ZMod 5` is read modulo 5, so `#eval` shows the representative `2`. How a numeral gets its meaning in a type is explained in {ref "ofnat"}[Where numerals come from].

In terms of sets, a function `f : (x : α) → β x` chooses one element `f x ∈ β x` for every `x`. It is an element of the product $`\prod_{x \in \alpha} \beta(x)`. This is where the name Π comes from.

## Polymorphic functions
%%%
tag := "polymorphic-functions"
number := false
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

Lean's own identity function is defined in its Prelude as

```
def id {α : Sort u} (a : α) : α := a
```

With `Sort u` instead of `Type u` it covers `Prop` as well, so `id h : P` for a proof `h : P`:

```lean
#check id (rfl : 1 = 1)   -- id rfl : 1 = 1
```

## Proofs as arguments
%%%
number := false
%%%

An argument may also be a proof. A division that demands a proof that the denominator is not zero cannot be called with zero:

```lean
def safeDiv (a b : ℤ) (_ : b ≠ 0) : ℤ := a / b

#eval safeDiv 10 3 (by decide)   -- 3
```

The third argument is a proof of `3 ≠ 0`, here written as a tactic proof `by decide` in the place of a term: `decide` proves a statement without variables by computing whether it holds. The type `(a b : ℤ) → b ≠ 0 → ℤ` of `safeDiv` is a Π-type, because the type of the proof depends on `b`.

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

*Use.* A term of an inductive type is used by distinguishing which constructor built it: *pattern matching*, the subject of {ref "pattern-matching-and-recursion"}[chapter 1.3]. Lean translates every pattern match into the type's *recursor* `MyNat.rec`, which the declaration also introduces.

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

Here `MyOption α` is a type for every type `α`.

Lean's `Option` is declared in the same way, and Mathlib builds on it. The natural numbers with `∞` are `ℕ` with one new element added, which `Option` does:

```lean
def MyENat : Type := Option ℕ
```

Here `none` plays the role of `∞`. Mathlib's `ℕ∞` (typed `\bN\infty`) is notation for `ENat`, defined as `WithTop ℕ`, and `WithTop α` is `Option α` with `none` read as a new largest element `⊤` (`#print ENat`, `#print WithTop`). So `ℕ∞` is `MyENat`, and `rfl` sees it:

```lean
example : ℕ∞ = MyENat := rfl
example : (⊤ : ℕ∞) = Option.none := rfl
example : (3 : ℕ∞) = Option.some 3 := rfl
```

The extended non-negative reals `ℝ≥0∞`, the values of a measure in {ref "measure-theory"}[Measure theory], are built the same way, as `WithTop ℝ≥0`.

Disjunction is an inductive type with two constructors: a proof of `P ∨ Q` is a proof of `P` or a proof of `Q`, marked by the constructor. Declared by hand:

```lean
inductive MyOr (a b : Prop) : Prop where
  | inl : a → MyOr a b
  | inr : b → MyOr a b

example (P Q : Prop) (hP : P) : MyOr P Q := .inl hP
```

Lean's `∨` is `Or`, declared in the same way. It is the disjoint union for propositions: the constructor records which side the proof came from. Conjunction `∧` has one constructor with two arguments; it is a structure, and comes in {ref "structures"}[Structures] below.

Inductive types are the main mechanism by which new data types enter Lean, and `Mathlib` uses them throughout.

# Structures
%%%
tag := "structures"
%%%

A *structure* is an inductive type with exactly one constructor, whose arguments are named fields. Many mathematical objects are of this kind. A point in the plane has an `x`-coordinate and a `y`-coordinate:

```lean
structure Point where
  x : ℕ
  y : ℕ
```

The declaration is essentially the same as

```
inductive Point where
  | mk : ℕ → ℕ → Point
```

Use `structure` for a type with a single constructor with named fields (points, complex numbers, algebraic structures), and `inductive` for a type with several constructors (natural numbers, lists, trees, `Option`, `Bool`).

*Formation.* The declaration introduces the type `Point : Type`.

*Construction.* There is a single constructor, `Point.mk`, so both fields must be supplied: `Point.mk 3 4` is a point.

*Use.* A field is read off with its *projection*: `Point.x p` is the `x`-coordinate of `p : Point`. A name such as `Point.x`, which begins with the name of a type, can also be written after a term of that type, separated by a dot: `p.x` means `Point.x p`.

*Computation.* A projection applied to a point built by the constructor returns the field: `(Point.mk 3 4).x` reduces to `3`.

```lean
#check (Point.mk : ℕ → ℕ → Point)
#check (Point.x : Point → ℕ)
example : (Point.mk 3 4).x = 3 := rfl
```

Like every inductive type, `Point` has a recursor, `Point.rec`. It takes a single case, a function of the fields, and the projections `Point.x` and `Point.y` are defined through it.

A value of a structure is determined by its fields: `p` and `Point.mk p.x p.y` are *definitionally* equal, so `rfl` proves it. This is the η rule of the {ref "reduction-rules"}[reduction rules], here *for structures*. For a general inductive type there is no such rule: `n : ℕ` is not definitionally `0` or a successor, and to split on it you need `cases`.

```lean
example (p : Point) : p = Point.mk p.x p.y := rfl
```

## Building structure values
%%%
tag := "structure-values"
number := false
%%%

Besides `Point.mk`, Lean has three more ways to call the constructor:

```lean
def origin : Point := { x := 0, y := 0 }
def p1 : Point := ⟨1, 2⟩
def p2 : Point := Point.mk 3 4
def p3 : Point where
  x := 0
  y := 0
```

They are the record form `{ x := …, y := … }`, the *anonymous constructor* `⟨...⟩` (typed `\<` and `\>`), the explicit `Point.mk`, and the *block* `where` form, one `field := value` line per field, with no braces or commas. The `where` form is just the record form spread over several lines; it has nothing to do with the `|`-branches of {ref "pattern-matching"}[pattern matching] below (fields are `field := value`, not `| pattern => …`).

Here the target type is fixed by the `: Point` on the left of `:=`, so Lean knows which constructor `{ … }` and `⟨…⟩` mean. When the type is *not* clear from the context, you can annotate the record itself:

```lean
#check ({ x := 0, y := 0 } : Point)
#eval p1.x          -- 1
#eval p1.y          -- 2
```

A new value can be built from an existing one, changing only some fields, with the `with` keyword:

```lean
def p4 : Point := { p1 with y := 10 }
-- p4.x = 1, p4.y = 10
```

Structures are immutable, so this creates a new `Point` rather than modifying `p1`.

## Defaults and extensions
%%%
number := false
%%%

Fields may be given *default values* as part of the declaration, and a value may then omit those fields:

```lean
-- the arithmetic progression a, a + d, a + 2d, ...
structure ArithProg where
  start : ℕ := 0
  step : ℕ := 1

def evens : ArithProg := { step := 2 }

#eval evens.start    -- 0 (the default)
#eval evens.step     -- 2
```

With both defaults, `{}` is the progression 0, 1, 2, … of all natural numbers.

One structure can *extend* another, inheriting all of its fields. A value supplies all fields, inherited and new:

```lean
structure Point3D extends Point where
  z : ℕ

def q : Point3D := { x := 1, y := 2, z := 3 }

#eval q.x    -- 1 (inherited from Point)
#eval q.z    -- 3
```

Mathlib builds its algebraic structures in this way: a commutative ring extends a ring, which extends a semiring.

## Operations
%%%
number := false
%%%

Operations on a structure are ordinary functions. If their name begins with the name of the type, they can be called with a dot, as projections are:

```lean
def Point.normSq (p : Point) : ℕ :=
  p.x * p.x + p.y * p.y

#eval p2.normSq    -- 25
```

`p2.normSq` (the squared distance from the origin) works because Lean sees that `p2 : Point` and looks for `Point.normSq`. A *Gaussian integer* (a complex number with integer parts) gives a fuller example, data and its operations together:

```lean
structure MyComplex where
  re : ℤ
  im : ℤ

def MyComplex.add (a b : MyComplex) : MyComplex :=
  { re := a.re + b.re, im := a.im + b.im }

def MyComplex.mul (a b : MyComplex) : MyComplex :=
  { re := a.re * b.re - a.im * b.im,
    im := a.re * b.im + a.im * b.re }

def i : MyComplex := { re := 0, im := 1 }

#eval (MyComplex.mul i i).re    -- -1
```

## Data with a property
%%%
number := false
%%%

A field may be a proof. Then a structure bundles *data together with a property*, here a map `ℤ → ℤ` together with a proof that it respects addition:

```lean
structure IntAddMap where
  toFun : ℤ → ℤ
  map_add : ∀ x y, toFun (x + y) = toFun x + toFun y

def triple : IntAddMap where
  toFun x := 3 * x
  map_add x y := mul_add 3 x y

#eval triple.toFun 4    -- 12
```

To build a term, both the function and the proof must be supplied. This pattern of bundling data with properties is how Mathlib organizes mathematics: a linear map, a continuous function and a group homomorphism are all structures of this kind.

`Fin n`, the type of the natural numbers less than `n`, is a structure of this kind as well. An element consists of a natural number `val` together with a proof `isLt` that it is less than `n`. Lean's Prelude declares

```
structure Fin (n : ℕ) where
  val : ℕ
  isLt : val < n
```

and the constructor `Fin.mk` takes both fields:

```lean
#check @Fin.mk
-- {n : ℕ} → (val : ℕ) → val < n → Fin n

example : Fin 3 := ⟨2, by decide⟩
example (n : ℕ) (h : 0 < n) : Fin n := ⟨0, h⟩
#eval (⟨2, by decide⟩ : Fin 3).val   -- 2
```

Two elements of `Fin n` are equal when their values are, which is `Fin.ext`. `Fin.last n` is the largest element of `Fin (n + 1)`, the pair of `n` and a proof of `n < n + 1`. Its type depends on `n`, so `Fin.last` is a dependent function in the sense of {ref "pi-types"}[Dependent functions] above:

```lean
#check @Fin.last   -- (n : ℕ) → Fin (n + 1)
example (a b : Fin 3) (h : a.val = b.val) : a = b :=
  Fin.ext h
```

`Fin.ext` needs no axiom. `cases` splits `a` and `b` into their fields; once the values agree, two proofs of `val < n` remain, and these are equal by `rfl`, because Lean does not distinguish proofs of the same proposition ({ref "prop-special"}[Why `Prop` is special]):

```lean
example {n : ℕ} (a b : Fin n) (h : a.val = b.val) :
    a = b := by
  cases a; cases b; cases h; rfl
```

Mathlib calls every lemma of the form "equal if the parts are equal" `.ext`: `Fin.ext`, `Prod.ext`, `Subtype.ext`. For functions the analogous statement, `funext`, does not follow from splitting into fields; it is discussed in {ref "axiom-funext"}[Function extensionality is a theorem].

## Conjunction
%%%
number := false
%%%

A proof of `P ∧ Q` consists of a proof of `P` and a proof of `Q`. Lean's Prelude declares `And` as a structure with the two fields `left` and `right`, both proofs:

```
structure And (a b : Prop) : Prop where
  intro ::
  left : a
  right : b
```

The line `intro ::` names the constructor `And.intro` instead of the default `And.mk`.

```lean
example (P Q : Prop) (hP : P) (hQ : Q) : P ∧ Q := ⟨hP, hQ⟩
example (P Q : Prop) (h : P ∧ Q) : Q ∧ P := ⟨h.2, h.1⟩
```

`P ∧ Q` is the pair of two proofs, as `α × β` is the pair of two data. The projections are `h.1` and `h.2`, also written `h.left` and `h.right`. Where `∧` is the pair, `∨` from {ref "inductive"}[Inductive types] is the disjoint union.

## Structures and inductive types
%%%
tag := "inductive-vs-structure"
number := false
%%%

The basic types of Lean are all inductive types, most of them twice: once in `Type` for data, once in `Prop` for propositions.

:::table (align := left) +header
* + constructors
  + data (`Type`)
  + proposition (`Prop`)
* + none
  + `Empty`
  + `False`
* + one, without arguments
  + `Unit`
  + `True`
* + two, without arguments
  + `Bool`
  + —
* + one, with two arguments (a structure)
  + `α × β`
  + `P ∧ Q`
* + two, with one argument each
  + `α ⊕ β`
  + `P ∨ Q`
* + one, with a value and a proof
  + `{x : α // P x}`
  + `∃ x, P x`
* + recursive
  + `ℕ`, `List α`
  + `n ≤ m` on `ℕ`
:::

`∃`, subtypes and `≤` are the subject of {ref "type-formers"}[chapter 1.4].
