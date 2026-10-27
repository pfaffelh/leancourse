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

#doc (Manual) "Types I: building types" =>
%%%
htmlSplit := .never
tag := "types"
%%%

Lean has the data types every programming language has — `int`, `string`, `float` — and you can define your own, as you will in this course. Throughout, `x : α` means that `x` is a term of type `α`: `false : Bool`, `42 : ℕ`, `f : ℕ → ℝ` for a function from ℕ to ℝ (itself a type), and `0 ≠ 1 : Prop` for the proposition that 0 and 1 differ. Terms and types can depend on variables, e.g. in `∀ (n : ℕ), n < n + 1 : Prop` (the term `n < n + 1` depends on `n : ℕ`) and `f : (n : ℕ) → (Fin n → ℝ)` where `Fin n` is the type which carries `{0, ..., n-1}` (here, the type `Fin n → ℝ` depends on `n : ℕ`), which is a function `f` with domain `ℕ` such that `f n ∈ ℝ^n`.

Two words for terms recur throughout, depending on their type: a term `h : P` whose type `P` is a `Prop` is called a *proof* (of `P`), while a term `a : α` whose type `α` is a `Type u` (where `u` will be called a universe) is called *data*. So `42 : ℕ` and `true : Bool` are data, whereas any term of the proposition `0 ≠ 1` is a proof of it. (The two kinds of universe, `Prop` and `Type u`, are the subject of the {ref "type-universes"}[last section].)

These data types are abstract: Lean treats `ℕ` and `ℝ` as genuinely infinite, not as floating-point approximations. `ℕ` is the `zero`/`succ` construction of the {ref "nat"}[introduction]; `ℝ` is built from an equivalence relation on Cauchy sequences, a {ref "quotient-types"}[quotient type]. As a consequence, `0 : ℕ` and `0 : ℝ` are different objects. Where a natural number is used as a real number, Lean inserts a conversion, a {ref "coercions"}[coercion], and displays it as `↑n`.

In Lean every object is a term, and every term has a type. A type is itself a term, so it has a type as well.

This chapter shows how types are built: function types, inductive types and structures, pairs, subtypes, type families and quotients. In several of them the type of one part depends on the value of another. Such types are called *dependent*, and they are what separates Lean from most programming languages. The rules behind the constructions are the subject of the {ref "rules"}[next chapter].

The [slides](slides/1-2-types/) for this chapter follow it section by section.

# Function types and Π-types
%%%
tag := "pi-types"
%%%

The function `fun n => n + 1` takes each `n : ℕ` to a term of type `ℕ`, so its type is `ℕ → ℕ`. A proof of `∀ n : ℕ, n < n + 1` takes each `n : ℕ` to a proof of `n < n + 1`. The two differ only in that the type of the value, `n < n + 1`, depends on `n`. Both are instances of one type former, the *dependent function type* or *Π-type* `(x : α) → β x`.

There are two notations for it. We write `(x : α) → β x`, or `α → β` if `β` does not mention `x`, when `β x` is data, and `∀ x : α, β x` when `β x` is a proposition. Lean prints them the same way. The two notations denote the same type, so `rfl` proves them equal:

```lean
#check (fun n => n + 1 : ℕ → ℕ)

example : ∀ n : ℕ, n < n + 1 :=
  fun n => Nat.lt_succ_self n

example : ((n : ℕ) → n < n + 1) =
    (∀ n : ℕ, n < n + 1) := rfl
```

A dependent function whose values are data: `Fin.last n` is the largest element of `Fin (n + 1)`, so each value lies in a different type.

```lean
def lastOf : (n : ℕ) → Fin (n + 1) :=
  fun n => Fin.last n

#check lastOf 3   -- lastOf 3 : Fin (3 + 1)
#eval lastOf 3    -- 3
```

The argument may itself be a type. The polymorphic identity takes a type `α` and returns the identity on `α`:

```lean
def polyId : (α : Type) → α → α :=
  fun _ a => a

#check polyId ℕ 42        -- ℕ
#check polyId String "hi" -- String
```

An argument may also be a proof. A division that demands a proof that the denominator is not zero cannot be called with zero:

```lean
def safeDiv (a b : ℤ) (_ : b ≠ 0) : ℤ := a / b

#eval safeDiv 10 3 (by norm_num)   -- 3
```

In terms of sets, a function `f : (x : α) → β x` chooses one element `f x ∈ β x` for every `x`. It is an element of the product $`\prod_{x \in \alpha} \beta(x)`. This is where the name Π comes from.

# Inductive types
%%%
tag := "inductive"
%%%

`Nat`, `List`, `Option`, `Bool` and `Empty` are all *inductive* types; `Nat` and `Bool` were dissected in the {ref "nat-intro"}[previous chapter]. What follows is how to declare such a type yourself, and which declarations Lean accepts.

You declare an inductive type by giving a name, the type's universe, and a list of *constructors*, each saying how to build a new element out of existing pieces. Declaring the natural numbers by hand reproduces exactly the structure of `Nat`:

```lean
inductive MyNat where
  | zero : MyNat
  | succ (n : MyNat) : MyNat
```

As with `Nat`, this single declaration introduces three things at once: the type `MyNat`; its two constructors `MyNat.zero` and `MyNat.succ`, so every element is either `zero` or `succ n`; and a *recursor* `MyNat.rec` — the type's *eliminator*, the counterpart of its constructors — of the same shape as `Nat.rec`, into which pattern matching, `cases`, and `induction` all translate. Its {ref "reduction-rules"}[iota rule], `MyNat.rec z s (.succ n) ⟶ s n (MyNat.rec z s n)`, is the firing we watched for `Nat`. And a recursor is not special to `inductive`: since a `structure` is a single-constructor inductive, it too has one — `Point.rec` (from the next section) takes a single case, a function of the fields, and the projections `Point.x`, `Point.y` are defined through it.

With {ref "type-universes"}[universes] available, the recursor can be stated in full generality. The introduction used its *non-dependent* form, into a fixed result type; the true `MyNat.rec` lets that type *depend* on the value being consumed, a dependency recorded by a *motive* `MyNat → Sort u` (the leading `@` in `@MyNat.rec` makes Lean's normally-hidden implicit arguments — here the `motive` — explicit, so that `#check` prints them; see {ref "strict-implicit"}[the appendix on parentheses]):

```lean
#check @MyNat.rec
-- {motive : MyNat → Sort u} →
--   motive .zero →                      -- zero case
--   ((n : MyNat) → motive n →
--      motive n.succ) →                 -- succ case
--   (t : MyNat) → motive t
```

With a data-valued `motive` this is the *recursion* the introduction showed; with a `Prop`-valued one it is precisely the *induction principle*. Recursion and induction are thus two readings of the single primitive `MyNat.rec` — which is why the `induction` tactic and recursive definitions feel so alike.

The declaration only *forms the type*. How to actually build its elements and *define functions* on it — typically by pattern matching on the constructors — is the subject of {ref "terms"}[the chapter on terms].

Proofs about an inductive type use the `induction` tactic, which applies the recursor for you: one subgoal per constructor, with an induction hypothesis for each recursive argument.

Inductive types also cover non-recursive data:

```lean
inductive Colour where
  | red | green | blue
```

and parameterized types:

```lean
-- `MyOption α` is either `none` or `some a` for some `a : α`.
inductive MyOption (α : Type) where
  | none : MyOption α
  | some (a : α) : MyOption α
```

Inductive types are the main mechanism by which new data types enter Lean, and `Mathlib` uses them throughout. They also settle the universe question from the other side: the universe of an inductive type must be large enough to hold all of its constructor arguments.

Not every `inductive` declaration is accepted. A constructor may mention the type being defined, but only *positively*. The *arrow* here is the `→` of a function type: in `α → β` the type `α` of the inputs stands to the left of the arrow, the type `β` of the values to the right. Strictly positive means that in the type of an argument of a constructor, the type being defined never stands to the left of an arrow. The type of the constructor itself does not count: every constructor ends in `→ MyTree`, and it is only the arguments before that last arrow that are checked. This *strict positivity* condition keeps inductive types well-founded and free of paradox. An *infinitely-branching* tree — where a `node` carries one subtree for each natural number — is fine, because the argument of `node` has type `ℕ → MyTree`, and there `MyTree` stands to the *right* of `→`:

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

The rejection is not pedantry: were `Bad` allowed, one could prove `False`. Project the stored function out of a `b : Bad` and apply it to `b` itself,

```
def app : Bad → (Bad → False) | .mk f => f
def neg (b : Bad) : False := app b b
```

so `neg : Bad → False`. Then `Bad.mk neg : Bad`, and `neg (Bad.mk neg) : False` is a closed proof of `False` (it even loops, `neg (Bad.mk neg) ⟶ neg (Bad.mk neg)` — the untyped Ω combinator smuggled into the theory). Strict positivity outlaws exactly the negative occurrence that ties this self-applying knot — the same consistency concern that rules out `Type : Type`. (That positivity is also *sufficient* for consistency — every strictly positive type is the least fixed point of a monotone functor, so the theory has a model — is a deep metatheorem, not something Lean proves about itself.)

# Structures
%%%
tag := "structures"
%%%

While inductive types let us define types with multiple constructors, many mathematical objects are better described as a *collection of named fields*. For example, a point in the plane has an `x`-coordinate and a `y`-coordinate. In Lean, we use `structure` for this.

A `structure` is a special case of an inductive type with exactly one constructor and named fields. Here is a simple example:

```lean
structure Point where
  x : ℕ
  y : ℕ
```

This declares a type `Point` whose elements are records with two `ℕ` fields. There is a single constructor, so both fields must be supplied. The declaration also produces that constructor `Point.mk` and one projection per field, whose types can be inspected without building a value:

```lean
#check (Point.mk : ℕ → ℕ → Point)
#check (Point.x : Point → ℕ)
#check (Point.y : Point → ℕ)
```

A value of a structure is determined by its fields: `p` and `Point.mk p.x p.y` are *definitionally* equal, so `rfl` proves it. This is the η rule of the {ref "reduction-rules"}[reduction rules], here *for structures*. It holds for every structure, for instance for pairs `ℕ × ℕ`:

```lean
example (p : Point) : p = Point.mk p.x p.y := rfl
example (p : ℕ × ℕ) : p = (p.1, p.2) := rfl
```

For a general inductive type there is no such rule: `n : ℕ` is not definitionally `0` or a successor, and to split on it you need `cases`.

Fields may be given *default values* as part of the declaration:

```lean
structure MyConfig where
  width : ℕ := 80
  height : ℕ := 24
  title : String := "Untitled"
```

These defaults are used whenever a value is built without specifying every field.

One structure can *extend* another, inheriting all of its fields:

```lean
structure Point3D extends Point where
  z : ℕ
```

so a `Point3D` has fields `x`, `y` (from `Point`) and `z`. This is particularly important in Mathlib, where the algebraic hierarchy uses structure extension extensively: `CommRing` extends `Ring`, which extends `Semiring`, and so on.

Structures are natural for representing mathematical objects. A *Gaussian integer* (a complex number with integer parts) is a pair of `ℤ`s,

```lean
structure MyComplex where
  re : ℤ
  im : ℤ
```

and a structure may bundle *data together with a property* — here a linear map, carrying both a function and a proof that it respects addition (the square brackets `[Add α]` are an *instance-implicit* argument, requiring `α` to carry an addition; see {ref "square-bracket-notation"}[the typeclasses chapter]):

```lean
structure MyLinearMap (α β : Type) [Add α] [Add β] where
  toFun : α → β
  map_add : ∀ x y : α, toFun (x + y) = toFun x + toFun y
```

This pattern of bundling data with properties is fundamental to how Mathlib organizes mathematics.

How to *construct* values of these types, read their fields, and define operations on them is the subject of {ref "terms"}[the chapter on terms].

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

but the `structure` version gives us named fields, {ref "structure-values"}[dot notation], the possibility for default values, and the `extends` mechanism. (A `class` is in turn a `structure` marked for use by instance search; we return to it in the {ref "typeclasses"}[Typeclass] chapter.)

# Pairs and Σ-types
%%%
tag := "sigma-types"
%%%

A *dependent pair* consists of a first component `a : α` and a second component `b : β a` whose type depends on `a`. Their type is the *Σ-type*, written `(x : α) × β x` or `Σ x : α, β x`. It is not a new primitive but a structure with two fields:

```lean
#print Sigma

def aPair : (n : ℕ) × Fin (n + 1) := ⟨3, Fin.last 3⟩

#eval aPair.1   -- 3
#check aPair.2  -- aPair.2 : Fin (aPair.fst + 1)
```

In terms of sets, the pairs `⟨a, b⟩` with a fixed `a` form the piece $`\{a\} \times \beta(a)`, and the Σ-type is the disjoint union of these pieces, $`\coprod_{x \in \alpha} \beta(x)`. Counting shows the difference to the Π-type: the Σ-type has $`\sum_x |\beta(x)|` elements, the Π-type $`\prod_x |\beta(x)|`.

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

The last column is the subject of {ref "curry-howard"}[the Curry-Howard correspondence]. `∃` is not literally a Σ-type: it forgets which witness was given ({ref "sigma-vs-exists"}[Σ and ∃]).

# Subtypes
%%%
tag := "subtypes"
%%%

The *subtype* `{x : α // P x}` is the Σ-type in which the second component is a proof: a pair of `x : α` and `h : P x`, where `P : α → Prop`. It represents elements of `α` satisfying predicate `P`. Since the second component is a proof (in `Prop`), subtypes enjoy proof irrelevance: two elements of `{x : α // P x}` are equal if and only if their first components are equal.

```lean
-- The type of natural numbers greater than 5
def BigNat : Type := {n : ℕ // n > 5}

def seven : BigNat := ⟨7, by norm_num⟩
def ten : BigNat := ⟨10, by norm_num⟩

-- We can extract the value
#eval seven.val  -- 7
```

This is how many mathematical objects are defined in Mathlib. For example, the type of prime numbers could be defined as `{n : ℕ // Nat.Prime n}`.

A subtype is closely related to, but distinct from, a *set* `s : Set α`: a set selects elements of `α` (which keep their type `α`), whereas the subtype `{x : α // P x}` is a *new* type. The relationship — including the coercion `↥s` from a set to its subtype of members — is spelled out in {ref "sets-and-types"}[the chapter on sets and types].

# Type families
%%%
tag := "type-families"
%%%

A *type family* is a function that returns a type, such as `Fin : ℕ → Type`. The second component of a Σ-type and the codomain of a Π-type are type families:

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
  ⟨5, by norm_num⟩
```

## Vectors indexed by length
%%%
tag := "vectors-indexed"
%%%

Vectors are the standard example: a vector of length `n` with entries in `α` is a function `Fin n → α`, where `Fin n` is the type with `n` elements (see the {ref "types"}[Types chapter]).

```lean
-- A vector of 3 natural numbers, represented as a function from Fin 3
def myVec : Fin 3 → ℕ := ![10, 20, 30]

#eval myVec 0   -- 10
#eval myVec 1   -- 20
#eval myVec 2   -- 30
```

The advantage of this representation is that indexing is *always safe*: you cannot access index 5 of a 3-element vector, because `5` is not a term of type `Fin 3`. The type system prevents out-of-bounds errors at compile time.

## Matrices as dependent types
%%%
tag := "matrices-dependent"
%%%

Matrices are a natural extension. An `m × n` matrix with entries in `α` can be represented as a function `Fin m → Fin n → α`, or equivalently as `Matrix (Fin m) (Fin n) α` in Mathlib:

```lean
-- A 2×3 matrix of natural numbers
def myMatrix : Fin 2 → Fin 3 → ℕ :=
  ![![1, 2, 3], ![4, 5, 6]]

#eval myMatrix 0 1  -- 2
#eval myMatrix 1 2  -- 6
```

In Mathlib, matrix multiplication is only defined when the dimensions match. If `A` is an `m × n` matrix and `B` is an `n × p` matrix, then `A * B` is an `m × p` matrix. The dependent types enforce that the inner dimensions agree — a dimension mismatch is a *type error*, caught at compile time.

# Quotient types
%%%
tag := "quotient-types"
%%%

The fourth way to form a type, after universes, function types and inductive types, is the *quotient*. Given a type `α` and a relation `r : α → α → Prop`, the type `Quot r` glues together elements that `r` relates: `α` seen up to `r`. This makes `ℝ` as Cauchy sequences up to equivalence an actual construction. `ℤ`, `ℚ`, `Multiset α` (lists up to reordering) and `ZMod n` are quotients too.

Its entire interface is four constants:

```lean
#check @Quot.mk     -- (r : α → α → Prop) → α → Quot r
#check @Quot.sound  -- r a b → Quot.mk r a = Quot.mk r b
#check @Quot.lift   -- (f : α → β) → (∀ a b, r a b → f a = f b) → Quot r → β
#check @Quot.ind
```

- `Quot.mk r` sends each element to its class.
- `Quot.sound` is the crux: if `r a b`, then the two classes are *the same term*. It is one of Lean's few genuine axioms — the `#print axioms name` command traces a constant back to the axioms it depends on, and here `#print axioms Quot.sound` reports `[Quot.sound]`.
- `Quot.lift` defines a function *out of* the quotient — but only once you *prove* it respects `r` (the `∀ a b, r a b → f a = f b` argument), which is exactly the mathematician's "check that this is well-defined". And it computes: `Quot.lift f h (Quot.mk r a)` reduces to `f a`.
- `Quot.ind` proves a property of every quotient element by checking it on the classes `Quot.mk r a`.

The computation rule of `Quot.lift` is a {ref "reduction-rules"}[reduction rule] of its own, like ι for recursors, so `rfl` proves it:

```lean
example (r : Nat → Nat → Prop) (f : Nat → Nat)
    (h : ∀ a b, r a b → f a = f b) (a : Nat) :
    Quot.lift f h (Quot.mk r a) = f a := rfl
```

In practice one usually goes through `Quotient`, a thin wrapper of `Quot` over a bundled equivalence relation (a `Setoid`). The status of `Quot.sound` as an axiom is taken up again in the {ref "axiom-quot"}[axioms chapter].

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

# The universe hierarchy
%%%
tag := "type-universes"
%%%

Every type is itself a term, so it has a type as well. These types-of-types (called *universes*) form a countably infinite tower, which is what keeps the system consistent.

At the bottom sit the two universes you meet first (Here, the `#check` command gives the type of a term):

```lean
#check (42 : ℕ)         -- a term ...
#check (ℕ : Type)       -- ... whose type ℕ lives in `Type`
#check ((2 = 2) : Prop) -- a proposition ...
#check (Prop : Type)    -- ... and `Prop` itself lives in `Type`
```

`Type` (which is the same as `Type 0`) is the universe of ordinary data types (`ℕ`, `ℝ`, `Bool`, `List α`, ...), and `Prop` (which is the universe of *propositions*, i.e. True/False-statements). But `Type` cannot contain itself — that would be paradoxical — so `Type` in turn lives in a larger universe `Type 1`, which lives in `Type 2`, and so on without end:

```lean
#check (Type 0 : Type 1)    -- `Type 0`, i.e. `Type`, lives in `Type 1`
#check (Type 1 : Type 2)    -- Type 1 : Type 2
```

:::example "The connection of `Type` to `Sort`"

The whole tower is captured by a single keyword `Sort`:

* `Sort 0` is `Prop`;
* `Sort 1` is `Type 0`, i.e. `Type`;
* `Sort (u+1)` is `Type u`.

```lean
example : Sort 0 = Prop := rfl
example : Sort 1 = Type := rfl
example : Type = Type 0 := rfl
```

So `Sort` is the umbrella that unifies `Prop` and all the `Type u`, and the one rule governing the hierarchy is `Sort u : Sort (u+1)`. There is deliberately no `Type : Type`; *why* this restriction is needed — it blocks a type-theoretic version of Russell's paradox — is taken up in the {ref "universe-determined"}[next chapter].
:::

:::example "Where types come from"
Types were introduced to stop a contradiction. Russell's set $`R = \{x : x \notin x\}` broke Frege's *Grundgesetze der Arithmetik* in 1902 ({ref "prehistory"}[Introduction]). Russell's repair of 1908 gave every object a type and let a type apply only to objects of lower type, so that `x ∈ x` is not false but not a statement at all. Zermelo's repair of the same year instead restricts which sets exist and leaves `x ∈ x` a formula. Mathematics followed Zermelo; proof assistants follow Russell, because a type checker can decide before any question of truth whether an expression means anything.

Alonzo Church turned the simple theory of types into a calculus in 1940, the simply typed lambda calculus on which *Isabelle/HOL* still rests. Dependent types, in which a type may mention a term, came with de Bruijn's Automath (1967) and Martin-Löf's type theory (1971). Coquand and Huet added impredicative quantification in the Calculus of Constructions (1985), and Paulin-Mohring added inductive types (1990). Lean's type theory is a variant of the result, the {ref "cic"}[Calculus of Inductive Constructions]. Three times the same thing happened: a system let an object be applied to itself, a contradiction followed, and types forbade it. In Lean the ban is visible as `Type 0 : Type 1 : Type 2 : ...`.
:::
