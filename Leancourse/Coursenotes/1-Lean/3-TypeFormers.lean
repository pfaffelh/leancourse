import VersoManual
import Manual.Meta
import Leancourse.Markup
import Mathlib

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open MyDef

set_option pp.rawOnError true

#doc (Manual) "Types and terms II: structures, pairs, subtypes, quotients" =>
%%%
htmlSplit := .never
tag := "type-formers"
%%%

The {ref "types"}[previous chapter] treated function types and inductive types. This chapter treats types whose terms bundle several components: structures, pairs and subtypes. Then come type families, functions whose values are types; indexed families and inductive predicates, type families defined by constructors; the logical connectives, which are these type formers with values in `Prop`; and quotients, types of equivalence classes. Each type former is again described in the four steps *Formation*, *Construction*, *Use* and *Computation*; a table at the end collects them.

The [slides](slides/1-3-type-formers/) for this chapter follow it section by section.

# Structures
%%%
tag := "structures"
%%%

Many mathematical objects are best described as a *collection of named fields*. A point in the plane has an `x`-coordinate and a `y`-coordinate. In Lean, we use `structure` for this:

```lean
structure Point where
  x : ℕ
  y : ℕ
```

A `structure` is an inductive type with exactly one constructor, whose arguments are named fields.

*Formation.* The declaration introduces the type `Point : Type`.

*Construction.* There is a single constructor, `Point.mk`, so both fields must be supplied: `Point.mk 3 4` is a point.

*Use.* A field is read off with its *projection*: `Point.x p` is the `x`-coordinate of `p : Point`. As for `MyNat.toNat` in the {ref "pattern-matching"}[previous chapter], this can also be written `p.x`.

*Computation.* A projection applied to a point built by the constructor returns the field: `(Point.mk 3 4).x` reduces to `3`.

```lean
#check (Point.mk : ℕ → ℕ → Point)
#check (Point.x : Point → ℕ)
example : (Point.mk 3 4).x = 3 := rfl
```

Being an inductive type, `Point` also has a recursor, `Point.rec`. It takes a single case, a function of the fields, and the projections `Point.x` and `Point.y` are defined through it.

A value of a structure is determined by its fields: `p` and `Point.mk p.x p.y` are *definitionally* equal, so `rfl` proves it. This is the η rule of the {ref "reduction-rules"}[reduction rules], here *for structures*. For a general inductive type there is no such rule: `n : ℕ` is not definitionally `0` or a successor, and to split on it you need `cases`.

```lean
example (p : Point) : p = Point.mk p.x p.y := rfl
```

## Building structure values
%%%
tag := "structure-values"
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

They are the record form `{ x := …, y := … }`, the *anonymous constructor* `⟨...⟩` (typed `\<` and `\>`), the explicit `Point.mk`, and the *block* `where` form, one `field := value` line per field, with no braces or commas. The `where` form is just the record form spread over several lines; it has nothing to do with the `|`-branches of pattern matching (fields are `field := value`, not `| pattern => …`).

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

`Fin n`, which appeared in the previous chapter, is a structure of this kind as well. An element consists of a natural number `val` together with a proof `isLt` that it is less than `n`, and the constructor `Fin.mk` takes both:

```lean
#check @Fin.mk
-- {n : ℕ} → (val : ℕ) → val < n → Fin n

example : Fin 3 := ⟨2, by simp⟩
example (n : ℕ) (h : 0 < n) : Fin n := ⟨0, h⟩
```

# Inductive types vs structures
%%%
tag := "inductive-vs-structure"
%%%

When should you use `inductive` and when `structure`?

* Use `structure` when your type has a single constructor with named fields. Examples: points, complex numbers, algebraic structures.
* Use `inductive` when your type has multiple constructors. Examples: natural numbers, lists, trees, `Option`, `Bool`.

A `structure` is syntactic sugar for an inductive type with one constructor. The definition

```
structure Point where
  x : ℕ
  y : ℕ
```

is essentially equivalent to

```
inductive Point where
  | mk : ℕ → ℕ → Point
```

but the `structure` version gives us named fields, the projections with dot notation, default values, and the `extends` mechanism.

# Pairs and Σ-types
%%%
tag := "sigma-types"
%%%

A *dependent pair* consists of a first component `a : α` and a second component `b : β a` whose type depends on `a`.

*Formation.* If `β x` is a type for every `x : α`, the *Σ-type* `(x : α) × β x`, also written `Σ x : α, β x`, is the type of these pairs. If `β` does not depend on `x`, it is the product `α × β`.

*Construction.* The pair is built with `⟨a, b⟩`, or `(a, b)` for the product.

*Use.* The components are read off with the projections `.1` and `.2`, also called `.fst` and `.snd`.

*Computation.* `⟨a, b⟩.1` reduces to `a` and `⟨a, b⟩.2` to `b`. A pair is determined by its components: `p = (p.1, p.2)` holds by `rfl`.

The Σ-type is not a new primitive but a structure with two fields:

```lean
#print Sigma

def aPair : (n : ℕ) × Fin (n + 1) := ⟨3, Fin.last 3⟩

#eval aPair.1   -- 3
#check aPair.2  -- aPair.2 : Fin (aPair.fst + 1)
example (p : ℕ × ℕ) : p = (p.1, p.2) := rfl
```

In terms of sets, the pairs `⟨a, b⟩` with a fixed `a` form the piece $`\{a\} \times \beta(a)`, and the Σ-type is the disjoint union of these pieces, $`\coprod_{x \in \alpha} \beta(x)`. Counting shows the difference to the Π-type: the Σ-type has $`\sum_x |\beta(x)|` elements, the Π-type $`\prod_x |\beta(x)|`. In Lean, `Fintype.card α` is the number of elements of a finite type `α`, and the tactic `decide` proves the two equations below by computing both sides:

```lean
-- Σ: 1 + 2 + 3 + 4 = 10 elements
example : Fintype.card
    ((n : Fin 4) × Fin (n + 1)) = 10 := by decide
-- Π: 1 · 2 · 3 · 4 = 24 elements
example : Fintype.card
    ((n : Fin 4) → Fin (n + 1)) = 24 := by decide
```

If `β` does not depend on `x`, all pieces are equal, and the Σ-type is the product `α × β`: the sum of $`|\alpha|` equal summands $`|\beta|`. The notation `×` for the dependent pair is named after this special case.

:::table (align := left) +header
* + non-dependent
  + dependent
  + in sets
  + for propositions
* + `α → β`
  + `(x : α) → β x`
  + $`\prod_x \beta(x)`
  + `∀ x, P x`
* + `α × β`
  + `(x : α) × β x`
  + $`\coprod_x \beta(x)`
  + `∃ x, P x`
:::

The last column is taken up in {ref "curry-howard"}[Propositions as types] below. `∃` is not literally a Σ-type: it forgets which witness was given.

# Subtypes
%%%
tag := "subtypes"
%%%

A *subtype* consists of the elements of a type `α` that satisfy a predicate `P : α → Prop`. It is a structure with two fields, an element and a proof:

```
structure Subtype {α : Sort u} (p : α → Prop) where
  val : α
  property : p val
```

*Formation.* `{x : α // P x}` is notation for `Subtype P`.

*Construction.* `⟨a, h⟩`, short for `Subtype.mk a h`, with `a : α` and `h : P a`.

*Use.* `s.val : α` is the element, `s.property : P s.val` the proof.

*Computation.* `⟨a, h⟩.val` reduces to `a`.

A subtype is the analogue of the Σ-type in which the second component is a proof rather than data. In Lean any two proofs of the same proposition are equal (*proof irrelevance*, built into the type theory). So two elements of a subtype are equal as soon as their first components are, which is `Subtype.ext`:

```lean
example (a b : {n : ℕ // 0 < n}) (h : a.val = b.val) :
    a = b :=
  Subtype.ext h

-- The type of natural numbers greater than 5
def BigNat : Type := {n : ℕ // n > 5}

def seven : BigNat := ⟨7, by simp⟩

#eval seven.val  -- 7
```

`Subtype` is one structure for all predicates, so its functions, such as `Subtype.ext`, apply to every subtype at once, and Lean converts an element of `{x : α // P x}` to an element of `α` by itself wherever one is expected. A structure of your own with the same two fields is a new type. `Fin n` is of this kind: it carries the same data as `{i : ℕ // i < n}`, and Mathlib has a bijection with inverse between the two, `Fin.equivSubtype : Fin n ≃ {i // i < n}`, but the two types are different. The separate type lets `Fin n` have operations of its own, such as arithmetic mod `n`.

This is how many mathematical objects are defined in Mathlib. For example, the type of prime numbers could be defined as `{n : ℕ // Nat.Prime n}`.

A subtype is closely related to, but distinct from, a *set* `s : Set α`: a set selects elements of `α` (which keep their type `α`), whereas the subtype `{x : α // P x}` is a *new* type. The relationship is spelled out in {ref "sets-and-types"}[the chapter on sets and types].

# Type families
%%%
tag := "type-families"
%%%

A *type family* is a function that returns a type, such as `Fin : ℕ → Type`. It is not a type former of its own but a function in the sense of the {ref "pi-types"}[previous chapter], whose values are types. The codomain of a Π-type and the second component of a Σ-type are type families:

```lean
-- A simple type family indexed by Bool
def BoolFamily : Bool → Type
  | true  => ℕ
  | false => String

-- Dependent function using the type family
def boolFamilyExample : (b : Bool) → BoolFamily b
  | true  => (42 : ℕ)
  | false => ("hello" : String)
```

In mathematical formalization, type families appear everywhere. For instance, the fiber of a function `f : α → β` over a point `b : β` is the subtype `{a : α // f a = b}`, which is a type family indexed by `β`.

```lean
-- The fiber of a function as a type family
def fiber (f : ℕ → ℕ) (b : ℕ) : Type :=
  {a : ℕ // f a = b}

-- An element of the fiber of (· * 2) over 10
def fiberExample : fiber (· * 2) 10 :=
  ⟨5, rfl⟩
```

*Vectors.* Vectors are the standard example: a vector of length `n` with entries in `α` is a function `Fin n → α`, where `Fin n` is the type with `n` elements. Mathlib writes `![a, b, c]` for the function on `Fin 3` with values `a`, `b`, `c`.

```lean
-- A vector of 3 natural numbers, as a function on Fin 3
def myVec : Fin 3 → ℕ := ![10, 20, 30]

#eval myVec 0   -- 10
#eval myVec 1   -- 20
#eval myVec 2   -- 30
```

The advantage of this representation is that indexing is *always safe*: you cannot access index 5 of a 3-element vector, because `5` is not a term of type `Fin 3`. The type system prevents out-of-bounds errors at compile time.

*Matrices.* Matrices are a natural extension. An `m × n` matrix with entries in `α` can be represented as a function `Fin m → Fin n → α`, or equivalently as `Matrix (Fin m) (Fin n) α` in Mathlib:

```lean
-- A 2×3 matrix of natural numbers
def myMatrix : Fin 2 → Fin 3 → ℕ :=
  ![![1, 2, 3], ![4, 5, 6]]

#eval myMatrix 0 1  -- 2
#eval myMatrix 1 2  -- 6
```

In Mathlib, matrix multiplication is only defined when the dimensions match. If `A` is an `m × n` matrix and `B` is an `n × p` matrix, then `A * B` is an `m × p` matrix. The dependent types enforce that the inner dimensions agree — a dimension mismatch is a *type error*, caught at compile time.

# Indexed families and inductive predicates
%%%
tag := "indexed-families"
%%%

A type family can also be declared with `inductive`. Then the constructors decide, for each value of the argument, which elements the type has. The standard example is the type of lists of length `n`:

```lean
inductive Vec (α : Type) : ℕ → Type where
  | nil : Vec α 0
  | cons {n : ℕ} (a : α) (v : Vec α n) : Vec α (n + 1)
```

The two arguments play different roles. `α`, written before the colon, is a *parameter*: it is the same in every constructor, and every constructor returns a `Vec α _`. The `ℕ` after the colon is an *index*: each constructor chooses its value, `nil` the index `0` and `cons` the index `n + 1`. `MyOption α` in the {ref "inductive"}[previous chapter] had a parameter and no index.

*Formation.* `Vec α n` is a type for every `α` and `n`; `Vec α : ℕ → Type` is a type family.

*Construction.* The constructors, with the indices they fix: `Vec.cons 1 (Vec.cons 2 .nil) : Vec ℕ 2`.

*Use.* Pattern matching, where only the constructors whose index fits are possible.

*Computation.* As for every inductive type, a match on a constructor takes its branch (ι).

The *Use* step is where indices pay off. The first element of a vector of length `n + 1` needs no case for `nil`, because `nil` has index `0`, which is not of the form `n + 1`:

```lean
def Vec.head {α : Type} {n : ℕ} : Vec α (n + 1) → α
  | .cons a _ => a

#eval (Vec.cons 1 (Vec.cons 2 .nil)).head   -- 1
```

*Inductive predicates.* If the family lands in `Prop`, the constructors are the rules by which a statement may be proved, and nothing else proves it. The even numbers:

```lean
inductive MyEven : ℕ → Prop where
  | zero : MyEven 0
  | add_two (n : ℕ) : MyEven n → MyEven (n + 2)

example : MyEven 4 := .add_two 2 (.add_two 0 .zero)
```

A hypothesis `h : MyEven k` is used with `cases h`, which produces one goal for each constructor whose index can equal `k`. For `k = 1` there is none, since `0 ≠ 1` and `n + 2 ≠ 1`, so `cases` closes the goal. For `k = n + 2` only `add_two` remains, and `cases` hands over its argument:

```lean
example : ¬ MyEven 1 := by
  intro h
  cases h

example (n : ℕ) (h : MyEven (n + 2)) : MyEven n := by
  cases h with
  | add_two _ h' => exact h'
```

Mathlib defines `Even n` differently, as `∃ r, n = r + r`. But `≤` on `ℕ` and equality itself are inductive predicates of exactly this kind:

```lean
#print Nat.le
#print Eq
```

`Nat.le n` has the constructors `refl : n ≤ n` and `step : n ≤ m → n ≤ m + 1`. `Eq a` has the parameter `a`, one index, and the single constructor `Eq.refl a : a = a`. So for `h : a = b`, `cases h` leaves only the case in which the index `b` is `a`: it replaces `b` by `a` everywhere. That is what rewriting with an equation rests on.

# Propositions as types
%%%
tag := "curry-howard"
%%%

A proposition `P : Prop` is a type, and a proof of `P` is a term `h : P`. A proposition is proved when a term of it has been built. The logical connectives are not added to Lean separately: they are the type formers of this chapter and the {ref "types"}[previous one], with values in `Prop`. This reading of propositions as types and proofs as terms is the *Curry-Howard correspondence* ({ref "types-history"}[Some history]).

## Implication, negation, and `∀`
%%%
tag := "forall-pi"
%%%

`P → Q` and `∀ x : α, P x` are the function types of the previous chapter: a proof of `P → Q` takes proofs of `P` to proofs of `Q` ({ref "term"}[Proofs of implications]), and a proof of `∀ x : α, P x` takes each `x : α` to a proof of `P x` ({ref "pi-types"}[Function types and Π-types]). Negation is defined from them: `¬P` is `P → False`.

```lean
example (P : Prop) : (¬P) = (P → False) := rfl

example (P : Prop) (hP : P) (hnP : ¬P) : False :=
  hnP hP
```

## `True` and `False`
%%%
tag := "false-true-types"
%%%

Both are inductive types, {ref "true-false"}[met in chapter 1.1]: `True` has the one constructor `True.intro`, `False` has none. So no term of `False` can be built from nothing. A `match` on `h : False` needs no branch, since there is no constructor to cover; `nomatch h` is this empty match. The result may have any type, which is *ex falso quodlibet*, available as `False.elim`:

```lean
example : True := True.intro

example (C : Prop) (h : False) : C := nomatch h
example (C : Prop) (h : False) : C := h.elim
```

## Conjunction
%%%
tag := "conjunction-product"
%%%

`P ∧ Q` is notation for `And P Q`, a structure with two fields:

```lean
#print And
```

*Formation.* `P ∧ Q`. *Construction.* `⟨hP, hQ⟩`, short for `And.intro hP hQ`. *Use.* The projections `h.1` and `h.2`, also `h.left` and `h.right`. *Computation.* `⟨hP, hQ⟩.1` reduces to `hP`. It is the product `α × β`, for propositions.

```lean
example (P Q : Prop) (hP : P) (hQ : Q) : P ∧ Q :=
  ⟨hP, hQ⟩

example (P Q : Prop) (h : P ∧ Q) : Q ∧ P :=
  ⟨h.2, h.1⟩
```

## Disjunction
%%%
tag := "disjunction-sum"
%%%

`P ∨ Q` is notation for `Or P Q`, an inductive type with two constructors:

```lean
#print Or
```

*Formation.* `P ∨ Q`. *Construction.* `Or.inl hP` from `hP : P`, or `Or.inr hQ` from `hQ : Q`. *Use.* Pattern matching with one branch per constructor, also available as `Or.elim`; in tactic mode `obtain hP | hQ := h`. *Computation.* A match on a constructor takes its branch.

```lean
example (P Q R : Prop) (h : P ∨ Q)
    (hPR : P → R) (hQR : Q → R) : R :=
  match h with
  | Or.inl hP => hPR hP
  | Or.inr hQ => hQR hQ

example (P Q R : Prop) (h : P ∨ Q)
    (hPR : P → R) (hQR : Q → R) : R :=
  h.elim hPR hQR
```

This is the disjoint union of `P` and `Q`, with one difference: the match may only prove propositions. A function `P ∨ Q → Bool` that tells which side holds is rejected; {ref "prop-special"}[Why `Prop` is special] gives the reason.

## The existential quantifier
%%%
tag := "exists-sigma"
%%%

`∃ x, P x` is notation for `Exists P`, an inductive type with one constructor that takes a witness and a proof:

```lean
#print Exists
```

*Formation.* `∃ x : α, P x`. *Construction.* `⟨a, h⟩` with `a : α` and `h : P a`. *Use.* Pattern matching, which gives a witness and a proof; in tactic mode `obtain ⟨x, hx⟩ := h`. *Computation.* A match on `⟨a, h⟩` takes its branch.

```lean
example : ∃ n : ℕ, n > 5 := ⟨7, by decide⟩

example (P Q : ℕ → Prop) (h : ∃ n, P n ∧ Q n) :
    ∃ n, Q n :=
  match h with
  | ⟨n, hn⟩ => ⟨n, hn.2⟩
```

A proof of `∃ x, P x` is a pair like an element of the {ref "sigma-types"}[Σ-type] or of the {ref "subtypes"}[subtype] `{x : α // P x}`. The difference is the universe. The subtype lives in `Type`, and its witness can be read off and computed with. `∃` lives in `Prop`, and as for `∨` the match may only prove propositions: the witness can be used inside proofs, but not to compute data.

```lean
def bigSeven : {n : ℕ // n > 5} := ⟨7, by decide⟩
#eval bigSeven.val   -- 7
```

Counting makes the difference visible. Any two proofs of a proposition are equal, so a proposition counts as 0 if false and 1 if true. The Σ-type has $`\sum_x |P(x)|` elements, one for each witness. `∃ x, P x` keeps only whether this sum is positive, that is, whether *some* `P x` holds. In the same way $`\prod_x |P(x)|` is positive exactly if *every* `P x` holds, which is `∀`. `∃` is the *propositional truncation* of the Σ-type: it forgets which witness was given. Getting a witness back needs the axiom of choice ({ref "rules"}[chapter 1.4]).

Use `∃` when only the existence matters, which is the usual case in mathematics, and a subtype when the witness is needed.

## The dictionary
%%%
tag := "curry-howard-summary"
%%%

:::table (align := left) +header
* + proposition
  + type former
  + a proof is
* + `P → Q`
  + function type
  + a function from proofs of `P` to proofs of `Q`
* + `∀ x : α, P x`
  + Π-type
  + a function taking each `x` to a proof of `P x`
* + `P ∧ Q`
  + structure, like `α × β`
  + a pair `⟨hP, hQ⟩`
* + `P ∨ Q`
  + inductive, like a disjoint union
  + `Or.inl hP` or `Or.inr hQ`
* + `∃ x : α, P x`
  + inductive, like a Σ-type
  + a pair `⟨a, h⟩` with `h : P a`
* + `True`
  + inductive, one constructor
  + `True.intro`
* + `False`
  + inductive, no constructor
  + there is none
* + `¬P`
  + `P → False`
  + a function from proofs of `P` to `False`
:::

A statement is a term of type `Prop` whether or not anyone has a proof. Goldbach's conjecture, with `Even` and `Nat.Prime` from Mathlib:

```lean
theorem goldbach : ∀ n : ℕ, n > 2 → Even n →
    ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ n = p + q := by
  sorry
```

A term that replaces the `sorry` is a proof of the conjecture.

# Quotient types
%%%
tag := "quotient-types"
%%%

The last way to form a type, after universes, function types and inductive types, is the *quotient*. Given a type `α` and a relation `r : α → α → Prop`, the type `Quot r` glues together elements that `r` relates: `α` seen up to `r`. This makes `ℝ` as Cauchy sequences up to equivalence an actual construction. `ℤ`, `ℚ`, `Multiset α` (lists up to reordering) and `ZMod n` (the integers mod `n`) are quotients too.

*Formation.* `Quot r` is a type.

*Construction.* `Quot.mk r a` is the class of `a : α`.

*Use.* `Quot.lift f h` defines a function *out of* the quotient from a function `f : α → β`, but only together with a proof `h` that `f` respects `r`, that is `∀ a b, r a b → f a = f b`. This is the mathematician's "check that this is well-defined". `Quot.ind` proves a property of every element of the quotient by checking it on the classes `Quot.mk r a`.

*Computation.* `Quot.lift f h (Quot.mk r a)` reduces to `f a`.

```lean
#check @Quot.mk     -- (r : α → α → Prop) → α → Quot r
#check @Quot.lift
-- (f : α → β) → (∀ a b, r a b → f a = f b) →
--   Quot r → β
#check @Quot.ind

example (r : Nat → Nat → Prop) (f : Nat → Nat)
    (h : ∀ a b, r a b → f a = f b) (a : Nat) :
    Quot.lift f h (Quot.mk r a) = f a := rfl
```

One property is missing from the four steps: related elements should have the *same* class. It does not follow from the rules, and Lean adds it as an *axiom*, a constant that is assumed without proof:

```lean
#check @Quot.sound  -- r a b → Quot.mk r a = Quot.mk r b
#print axioms Quot.sound   -- [Quot.sound]
```

`#print axioms name` lists the axioms that a constant depends on. In practice one usually goes through `Quotient`, a thin wrapper of `Quot` for a relation that is an equivalence relation; such a relation, bundled with the proof that it is one, is called a `Setoid`.

::::keepEnv
:::example "How `ℝ` is built as a quotient"
Mathlib's real numbers are a concrete instance of exactly this construction. First, a `CauSeq` is a {ref "subtypes"}[*subtype*]: the notation `{ f : ℕ → ℚ // IsCauSeq abs f }` means a rational sequence `f : ℕ → ℚ` bundled with a proof that it is Cauchy.

```lean
#check (CauSeq ℚ abs)
-- CauSeq ℚ abs = { f : ℕ → ℚ // IsCauSeq abs f }
example (f : CauSeq ℚ abs) : ℕ → ℚ := f.1
```

`ℝ` is then a one-field structure wrapping the *quotient* of these sequences by the relation "the difference tends to `0`". The class map `CauSeq.Completion.mk` is the `Quot.mk` of that quotient:

```lean
#check @Real.ofCauchy
-- CauSeq.Completion.Cauchy abs → ℝ

#check @CauSeq.Completion.mk
-- CauSeq ℚ abs → CauSeq.Completion.Cauchy abs

-- two sequences give the same real iff (f - g) → 0;
-- `≈` is the Setoid equivalence relation on `CauSeq`
example (f g : CauSeq ℚ abs) :
    f ≈ g ↔ (f - g).LimZero := Iff.rfl
```

Addition is the first use of `Quot.lift`. Two reals are added by adding *representative* sequences termwise, which is well-defined because `+` respects the relation: `f ≈ f'` and `g ≈ g'` give `f + g ≈ f' + g'`. With that checked, `Quot.lift` yields the computation rule that `mk` is an additive homomorphism:

```lean
example (f g : CauSeq ℚ abs) :
    CauSeq.Completion.mk f + CauSeq.Completion.mk g
      = CauSeq.Completion.mk (f + g) :=
  CauSeq.Completion.mk_add f g
```

This `mk (f) + mk (g) = mk (f + g)` equation *is* the `Quot.lift f h (Quot.mk r a) ⟶ f a` reduction from the {ref "reduction-rules"}[reduction rules], applied to a two-argument operation.
:::
::::

# The four steps at a glance
%%%
tag := "four-steps"
%%%

:::table (align := left) +header
* + type
  + formation
  + construction
  + use
  + computation
* + function
  + `(x : α) → β x`
  + `fun x => e`
  + `f a`
  + `(fun x => e) a ⟶ e[x := a]`
* + inductive
  + `inductive T`
  + constructors
  + pattern matching, `T.rec`
  + a match on a constructor takes its branch
* + structure
  + `structure S`
  + `⟨a, b⟩`, `{ x := a, … }`
  + projections `s.x`
  + `(S.mk a b).x ⟶ a`
* + Σ-type
  + `(x : α) × β x`
  + `⟨a, b⟩`
  + `.1`, `.2`
  + `⟨a, b⟩.1 ⟶ a`
* + subtype
  + `{x : α // P x}`
  + `⟨a, h⟩`
  + `.val`, `.property`
  + `⟨a, h⟩.val ⟶ a`
* + indexed family
  + `inductive T : I → Sort u`
  + constructors, each fixing an index
  + pattern matching, `cases`
  + a match on a constructor takes its branch
* + quotient
  + `Quot r`
  + `Quot.mk r a`
  + `Quot.lift f h`
  + `Quot.lift f h (Quot.mk r a) ⟶ f a`
:::

Here `e[x := a]` is `e` with `a` in place of `x`. Universes have only a formation step, `Sort u`. The {ref "rules"}[next chapter] states these steps as the rules of Lean's type theory.
