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

#doc (Manual) "Types and terms I: functions, inductive types, structures" =>
%%%
htmlSplit := .never
tag := "types"
%%%

Lean has the data types every programming language has — `int`, `string`, `float` — and you can define your own, as you will in this course. Throughout, `x : α` means that `x` is a term of type `α`: `false : Bool`, `42 : ℕ`, `f : ℕ → ℝ` for a function from ℕ to ℝ (itself a type), and `0 ≠ 1 : Prop` for the proposition that 0 and 1 differ. Terms and types can depend on variables, e.g. in `∀ (n : ℕ), n < n + 1 : Prop` (the term `n < n + 1` depends on `n : ℕ`) and `f : (n : ℕ) → ZMod n`, a function whose value at `n` lies in ℤ/nℤ (the type `ZMod n` of the value depends on `n : ℕ`).

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

See {ref "four-steps"}[The four steps at a glance] at the end of chapter 1.3 for a table of all type formers in these four steps.

The four steps are the four kinds of rule of Lean's type theory, stated formally in {ref "rules"}[chapter 1.4]. This chapter treats universes, function types, inductive types and structures; the {ref "type-formers"}[next chapter] dependent pairs, subtypes, type families and quotients. In several of these types the type of one part depends on the value of another. Such types are called *dependent*, and they are what separates Lean from most programming languages.

The [slides](slides/1-2-types/) for this chapter follow it section by section.

# Commands for terms
%%%
tag := "naming-terms"
%%%

Six commands recur in every chapter.

* `#check t` prints the type of the term `t`.
* `def name : T := t` gives the name `name` to the term `t`, after checking that `t` has type `T`.
* `theorem name : P := p` does the same for a proposition `P` and a proof `p` of it. Mathlib also accepts `lemma`, with the same meaning; Lean itself knows only `theorem`.
* `example : T := t` checks that `t` has type `T`, without giving it a name.
* `#eval t` computes the value of `t` and prints it. It runs compiled code; `rfl` instead asks the kernel to reduce ({ref "defeq"}[Definitional equality]), and for the definitions of this chapter both give the same value.
* `#print name` prints the definition of `name`.

```lean
#check 2 + 2           -- 2 + 2 : ℕ
def four : ℕ := 2 + 2
theorem four_eq : four = 4 := rfl
example : four = 4 := rfl
#eval four             -- 4
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

## Finding theorems
%%%
tag := "finding-theorems"
number := false
%%%

Mathlib has about 189 000 theorems. Their names follow fixed conventions, such as `mul_comm` for `a * b = b * a` or `le_of_lt` for `a < b → a ≤ b` ({ref "naming-conventions"}[Naming conventions]), but more often one knows the statement and not the name. Then search:

:::table (align := left) +header
* + tool
  + searches for
* + `exact?`
  + a theorem that closes the current goal
* + `apply?`
  + a theorem whose conclusion fits the goal; its hypotheses become new goals
* + `rw?`
  + an equation that rewrites the goal
* + `#loogle pattern`
  + theorems whose statement has the given form, e.g. `#loogle ?a * ?b = ?b * ?a`
* + `#leansearch "text"`
  + theorems matching a description in English
:::

The first three are tactics. They search with the current goal and hypotheses and print a suggestion, which replaces them in the finished proof:

```lean
example (a b : ℕ) : a * b = b * a := by
  exact?
```

`#loogle` and `#leansearch` are commands. They send the query to the services [Loogle](https://loogle.lean-lang.org/) and [LeanSearch](https://leansearch.net/), which can also be used in the browser, and so need an internet connection. Loogle is exact when the form of the statement is known; LeanSearch helps when one does not know the words Mathlib uses. More on searching, the documentation of Mathlib and where to ask is in {ref "navigating-mathlib"}[Navigating Mathlib].

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

So `Sort` covers `Prop` and all the `Type u`, and the one rule governing the hierarchy is `Sort u : Sort (u+1)`; in particular `Prop : Type`. In signatures you will often see `{α : Type*}`: `α` is a type in some universe `Type u`, and Lean introduces the universe variable `u` itself ({ref "polymorphic-functions"}[Polymorphic functions] below). Of the four steps, universes have only the first: `Sort u` is a type, and its terms are the types built in the rest of this chapter and the next.

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
#eval (fun x : ℕ ↦ x + 1) 5       -- 6
#eval (fun x y : ℕ ↦ x * y) 3 4   -- 12
```

Shorter still is the `·` placeholder (a centered dot, typed `\cdot`), which stands for an anonymous argument: `(· + 10)` is shorthand for `fun x ↦ x + 10`, and several `·` become successive arguments, so `(· + ·)` means `fun x y ↦ x + y`.

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

A dependent function whose values are data: Mathlib's `ZMod n` is the type ℤ/nℤ of integers modulo `n` (with `ZMod 0 = ℤ`). The function `sevenMod` takes `n` to the residue class of `7` in ℤ/nℤ. Its definition reads `7` for every `n`, but each value lies in a different type and is a different element there:

```lean
def sevenMod : (n : ℕ) → ZMod n :=
  fun _ => 7

#check sevenMod 5   -- sevenMod 5 : ZMod 5
#eval sevenMod 5    -- 2
#eval sevenMod 0    -- 7
```

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

Here `MyOption α` is a type for every type `α`.

Disjunction is an inductive type with two constructors: a proof of `P ∨ Q` is a proof of `P` or a proof of `Q`, marked by the constructor. Declared by hand:

```lean
inductive MyOr (a b : Prop) : Prop where
  | inl : a → MyOr a b
  | inr : b → MyOr a b

example (P Q : Prop) (hP : P) : MyOr P Q := .inl hP
```

Lean's `∨` is `Or`, declared in the same way. It is the disjoint union for propositions: the constructor records which side the proof came from.

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

but the `structure` version also gives the fields names, projections with dot notation, default values and the `extends` mechanism. Use `structure` for a type with a single constructor with named fields (points, complex numbers, algebraic structures), and `inductive` for a type with several constructors (natural numbers, lists, trees, `Option`, `Bool`).

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
structure MyConfig where
  width : ℕ := 80
  height : ℕ := 24
  title : String := "Untitled"

def myConfig : MyConfig := { title := "My Window" }
-- myConfig.width = 80, myConfig.height = 24
```

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

`Fin n`, the type of the natural numbers less than `n`, is a structure of this kind as well. An element consists of a natural number `val` together with a proof `isLt` that it is less than `n`, and the constructor `Fin.mk` takes both:

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

## Conjunction
%%%
number := false
%%%

A proof of `P ∧ Q` consists of a proof of `P` and a proof of `Q`. Lean declares `And` as a structure with the two fields `left` and `right`, both proofs:

```lean
#print And
-- structure And (a b : Prop) : Prop
--   And.left : a
--   And.right : b

example (P Q : Prop) (hP : P) (hQ : Q) : P ∧ Q := ⟨hP, hQ⟩
example (P Q : Prop) (h : P ∧ Q) : Q ∧ P := ⟨h.2, h.1⟩
```

`P ∧ Q` is the pair of two proofs, as `α × β` is the pair of two data. The constructor is `And.intro`, the projections are `h.1` and `h.2`, also written `h.left` and `h.right`. Where `∧` is the pair, `∨` from {ref "inductive"}[Inductive types] is the disjoint union.

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

`∃`, subtypes and `≤` are the subject of the {ref "type-formers"}[next chapter].

# Pattern matching and recursion
%%%
tag := "pattern-matching-and-recursion"
%%%

A term of an inductive type is used by asking which constructor built it. This section is about the functions defined in this way: by pattern matching, by recursion, and by the recursor itself. Structures are included, as inductive types with a single constructor.

## Pattern matching
%%%
tag := "pattern-matching"
number := false
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

Writing plain `zero` in place of `.zero` would fail: there is no `zero` in scope, only `MyNat.zero`. As for `Point.x`, for `m : MyNat` the name `m.toNat` means `MyNat.toNat m`.

A function can also be defined with the recursor directly, as `myDouble` was defined with `Nat.rec` in the {ref "nat-intro"}[previous chapter]: one argument for each constructor, and for `succ` the value on the predecessor is handed over as `d`. Lean's compiler, which runs `#eval`, does not support the recursors of your own types (for `Nat` it has special support), so the definition has to be marked `noncomputable`. The kernel reduces it all the same, so `rfl` works, and induction shows that it agrees with the version by pattern matching:

```lean
noncomputable def MyNat.double' (n : MyNat) : MyNat :=
  MyNat.rec .zero (fun _ d => .succ (.succ d)) n

example :
    MyNat.double' (.succ .zero) = .succ (.succ .zero) :=
  rfl

example (n : MyNat) : n.double' = n.double := by
  induction n with
  | zero => rfl
  | succ n ih =>
    show MyNat.succ (MyNat.succ n.double') = _
    rw [ih]
    rfl
```

Pattern matching is translated into the recursor for the kernel and into running code for `#eval`. That is why functions are usually written by pattern matching.

Pattern matching works for any inductive type. A list is empty, or a first element followed by a list. In Lean's library (`u` is a universe variable, {ref "polymorphic-functions"}[above]):

```
inductive List (α : Type u) where
  | nil : List α                              -- written []
  | cons (a : α) (l : List α) : List α        -- written a :: l
```

So `[1, 2, 3]` is notation for `1 :: 2 :: 3 :: []`, that is `List.cons 1 (List.cons 2 (List.cons 3 List.nil))`. A function on lists has a branch for `[]` and one for `a :: l`. The pattern `_` matches anything and names nothing.

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
number := false
%%%

The definitions above are *recursive*: they call themselves on smaller inputs. A classic example with two base cases is the Fibonacci sequence:

```lean
def fib : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | n + 2 => fib n + fib (n + 1)

#eval fib 10    -- 55
```

Lean checks that the three patterns cover every natural number. The numerals in the patterns stand for constructors: `0` is `Nat.zero`, `1` is `Nat.succ Nat.zero`, and `n + 2` is `Nat.succ (Nat.succ n)`. Lean splits the argument by its constructor, `zero` or `succ m`, and splits `m` again where a pattern requires it. Every branch of this case distinction must be reached by one of the patterns. With the line for `1` missing, the case `Nat.succ Nat.zero` is reached by none:

```lean +error
def fib' : ℕ → ℕ
  | 0 => 0
  | n + 2 => fib' n + fib' (n + 1)
```

The error is "Missing cases: (Nat.succ Nat.zero)". A pattern that can never be reached, because earlier patterns already cover it, is an error as well ("Redundant alternative").

Lean only accepts a recursive definition once it is convinced the recursion *terminates*. There are two ways:

* *Structural recursion.* Every recursive call is on a part of the input, that is, on an argument of the constructor that built it. Lean translates the definition into the recursor of the type (more precisely into `brecOn`, a packaging of the recursor), and there is nothing to prove.
* *Well-founded recursion.* Every recursive call makes a *measure* smaller, a natural number computed from the arguments. Lean translates the definition into `WellFounded.fix` and needs a proof that the measure decreases.

`factorial`, `length'` and `fib` are structural. In `fib (n + 2)` the calls are `fib n` and `fib (n + 1)`, both on parts of `n + 2`. So `fib` is translated into the recursor `Nat.rec` of the {ref "nat-intro"}[previous chapter], it computes by ι, and `rfl` checks values:

```lean
-- fib 3 ⟶ fib 1 + fib 2 ⟶ 1 + (fib 0 + fib 1) ⟶ 1 + (0 + 1)
example : fib 3 = 2 := rfl
```

Recursion on several parts works the same way. In a binary tree whose nodes carry a natural number, every node has two subtrees, and the height recurses on both:

```lean
inductive BinTree where
  | leaf : BinTree
  | node (l : BinTree) (a : ℕ) (r : BinTree) : BinTree

def BinTree.height : BinTree → ℕ
  | .leaf => 0
  | .node l _ r => max l.height r.height + 1

example : (BinTree.node .leaf 3
    (.node .leaf 4 .leaf)).height = 2 := rfl
```

A call that is not on a smaller argument is rejected. `def bad (n : ℕ) : ℕ := bad n + 1` fails to compile; were it accepted, `bad 0 = bad 0 + 1` would give `0 = 1`.

When a recursive call is not on a part of the input, Lean cannot translate the definition structurally and looks for a measure. Often it finds one on its own. In `log2` the argument shrinks from `n` to `n / 2`, and Lean proves `n / 2 < n` from `2 ≤ n`. The definition uses a *dependent* `if`: in `if h : c then a else b`, the proof `h : c` is available in `a`, and a proof of `¬c` in `b`.

```lean
def log2 (n : Nat) : Nat :=
  if _h : 2 ≤ n then 1 + log2 (n / 2) else 0

#eval log2 16   -- 4
```

Cantor's enumeration of `ℕ × ℕ` runs through the pairs diagonal by diagonal: `(0, 0)`; `(0, 1)`, `(1, 0)`; `(0, 2)`, `(1, 1)`, `(2, 0)`; and so on. `pairIndex m n` is the position of `(m, n)` in this list. Within a diagonal it steps back from `(m + 1, n)` to `(m, n + 1)`; from the first pair `(0, n + 1)` of a diagonal it steps back to the last pair `(n, 0)` of the previous one:

```lean
def pairIndex : ℕ → ℕ → ℕ
  | 0, 0 => 0
  | 0, n + 1 => pairIndex n 0 + 1
  | m + 1, n => pairIndex m (n + 1) + 1
termination_by m n => (m + n, m)
decreasing_by all_goals (rw [Prod.lex_def]; omega)

#eval pairIndex 2 1   -- 8
```

Here Lean needs help. No argument decreases in both recursive calls, and the sum `m + n` stays the same in the third line. Without the last two lines of the definition Lean reports "Could not find a decreasing measure". The measure is a pair: first the diagonal `m + n`, then the position `m` on it. Pairs are compared *lexicographically*: `(a, b)` is smaller than `(c, d)` if `a < c`, or if `a = c` and `b < d`. `termination_by` names the measure; `m n =>` names the two arguments, which the patterns leave unnamed. `decreasing_by` proves that the measure decreases. There is one goal for each recursive call, and `all_goals` applies the same tactics to both: `rw [Prod.lex_def]` replaces the lexicographic order by its definition, and `omega`, a tactic that proves linear arithmetic over `ℕ` and `ℤ`, finishes.

Sometimes Lean finds the measure but cannot prove that it decreases. For the logarithm to base `b` it has to show `n / b < n`. For `b = 2` this is linear arithmetic, which Lean does by itself; for a variable `b` it is not, and Lean stops with this goal. `decreasing_by` supplies the proof, here with the library theorem `Nat.div_lt_self : 0 < n → 1 < k → n / k < n`:

```lean
def logb (b n : ℕ) : ℕ :=
  if h : 2 ≤ b ∧ b ≤ n then 1 + logb b (n / b)
  else 0
decreasing_by exact Nat.div_lt_self (by omega) h.1

#eval logb 10 1000   -- 3
```

The theory behind well-founded recursion, what makes a relation well-founded and why `<` on `Nat` qualifies, is in {ref "wf-acc"}[Accessibility and well-founded relations]. If `decreasing_by` is left out, Lean tries a standard tactic, `decreasing_tactic`, which handles the simple cases on its own.

## Proving things about recursive definitions
%%%
tag := "recursive-proofs"
number := false
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
%%%
number := false
%%%

The {ref "nat-intro"}[previous chapter] used the recursor `Nat.rec` in a *non-dependent* form, into a fixed result type. In general the result type may *depend* on the term being consumed. This dependency is recorded by a *motive* `T → Sort u`. The binary tree `BinTree` from {ref "recursion"}[Recursion and termination] shows the full form:

```lean
#check @BinTree.rec
-- {motive : BinTree → Sort u} →
--   motive .leaf →                       -- leaf case
--   ((l : BinTree) → (a : ℕ) → (r : BinTree) →
--      motive l → motive r →
--      motive (.node l a r)) →            -- node case
--   (t : BinTree) → motive t
```

The case for `node` receives the three arguments of the constructor and, for the two subtrees `l` and `r`, the values `motive l` and `motive r` already computed for them. With the constant motive `fun _ => ℕ` this is recursion, for instance the sum of all numbers in a tree:

```lean
noncomputable def BinTree.sum : BinTree → ℕ :=
  BinTree.rec 0 (fun _ a _ sl sr => sl + a + sr)

example : (BinTree.node .leaf 3
    (.node .leaf 4 .leaf)).sum = 7 := rfl
```

With a `Prop`-valued motive the same recursor is the *induction principle* for trees: to prove a statement for every tree, prove it for `leaf`, and prove it for `node l a r` assuming it for `l` and for `r`. Those are two induction hypotheses, one for each subtree. Recursion and induction are two readings of the single primitive `BinTree.rec`, which is why the `induction` tactic and recursive definitions feel so alike. The `induction` tactic applies the recursor for you: one subgoal per constructor, with an induction hypothesis for each recursive argument.

Lean generates `T.rec` for every `inductive` declaration from its constructors, always by the same recipe:

1. The parameters of `T`, such as `α` in `MyOption α`, as implicit arguments.
2. The *motive* `motive : T → Sort u`, the type of the result, which may depend on the term.
3. One *case* per constructor, in the order of the declaration. For a constructor `c (a₁ : A₁) … (aₖ : Aₖ) : T` the case takes the arguments `a₁ … aₖ`, then, for every argument `aᵢ` of type `T` itself (a *recursive* argument), a value of `motive aᵢ`, and returns a value of `motive (c a₁ … aₖ)`.
4. The term `t : T` to be consumed; the result has type `motive t`.

With the recursor come its computation rules, one per constructor: applied to `c a₁ … aₖ`, the recursor takes the case for `c`, and passes it the arguments and, for each recursive argument `aᵢ`, the recursor applied to `aᵢ`. For `BinTree` the rule for `node` is `BinTree.rec z s (.node l a r) ⟶ s l a r (BinTree.rec z s l) (BinTree.rec z s r)`.

```lean
#check @Colour.rec
-- {motive : Colour → Sort u} →
--   motive .red → motive .green → motive .blue →
--   (t : Colour) → motive t
#check @MyOption.rec
-- {α : Type} → {motive : MyOption α → Sort u} →
--   motive .none →
--   ((a : α) → motive (.some a)) →
--   (t : MyOption α) → motive t
#check @List.rec
-- {α : Type v} → {motive : List α → Sort u} →
--   motive [] →
--   ((head : α) → (tail : List α) →
--      motive tail → motive (head :: tail)) →
--   (t : List α) → motive t
#check @Point.rec
-- {motive : Point → Sort u} →
--   ((x y : ℕ) → motive { x := x, y := y }) →
--   (t : Point) → motive t
```

The constructors of `Colour` have no arguments, so its cases are plain values and `Colour.rec` is a case distinction with three branches. `MyOption.some` has an argument `a : α` that is not recursive, so its case is a function of `a` and gets no value of the motive. `List.cons` has the recursive argument `tail`, and its case gets `motive tail`, the result for the rest of the list; read as a proof, this is the induction hypothesis. A structure has a single constructor, so `Point.rec` just unpacks the fields. For an inductive type in `Prop` with more than one constructor, such as `MyOr`, the motive may only take values in `Prop` ({ref "prop-special"}[Why `Prop` is special]).

## Strict positivity
%%%
number := false
%%%

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
