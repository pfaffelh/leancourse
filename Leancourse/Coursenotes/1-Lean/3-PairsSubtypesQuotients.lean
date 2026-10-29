import VersoManual
import Manual.Meta
import Leancourse.Markup
import Mathlib

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open MyDef

set_option pp.rawOnError true

#doc (Manual) "Types and terms II: pairs, subtypes, families, quotients" =>
%%%
htmlSplit := .never
tag := "type-formers"
%%%

The {ref "types"}[previous chapter] treated function types, inductive types and structures. This chapter treats dependent pairs and subtypes, whose terms bundle a value with data or a proof about it. Then come type families, functions whose values are types; indexed families and inductive predicates, type families defined by constructors; the logical connectives, which are these type formers with values in `Prop`; and quotients, types of equivalence classes. Each type former is again described in the four steps *Formation*, *Construction*, *Use* and *Computation*; a table at the end collects them.

The [slides](slides/1-3-pairs-subtypes-quotients/) for this chapter follow it section by section.

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

A subtype is the analogue of the Σ-type in which the second component is a proof rather than data. In Lean any two proofs of the same proposition are equal (*proof irrelevance*, built into the type theory; see {ref "prop-special"}[Why `Prop` is special] for reference). So two elements of a subtype are equal as soon as their first components are, which is `Subtype.ext`:

```lean
example (a b : {n : ℕ // 0 < n}) (h : a.val = b.val) :
    a = b :=
  Subtype.ext h

-- The type of natural numbers greater than 5
def BigNat : Type := {n : ℕ // n > 5}

def seven : BigNat := ⟨7, by decide⟩

#eval seven.val  -- 7
```

`Subtype` is one structure for all predicates, so its functions, such as `Subtype.ext`, apply to every subtype at once, and Lean converts an element of `{x : α // P x}` to an element of `α` by itself wherever one is expected (a *coercion*; see {ref "coercions"}[Coercions] for reference). A structure of your own with the same two fields is a new type. `Fin n` is of this kind: it carries the same data as `{i : ℕ // i < n}`, and Mathlib has a bijection between the two, but the two types are different. The separate type lets `Fin n` have operations of its own, such as arithmetic mod `n`.

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
number := false
%%%

For propositions `P` and `Q`, `P → Q` is a function type like any other, and a proof of `P → Q` is a function that takes a proof of `P` to a proof of `Q`. Modus ponens is function application, and chaining two implications is composition. In tactic mode, `intro` builds the `fun` and `exact` supplies the application ({ref "term"}[Tactic mode and term mode]):

```lean
example (P Q : Prop) (hP : P) (hPQ : P → Q) : Q :=
  hPQ hP

example (P Q R : Prop) :
    (P → Q) → (Q → R) → (P → R) :=
  fun hPQ hQR hP => hQR (hPQ hP)
```

A proof of `∀ x : α, P x` takes each `x : α` to a proof of `P x`: it is a dependent function ({ref "pi-types"}[Function types and Π-types]). Negation is defined from implication: `¬P` is `P → False`.

```lean
example (P : Prop) : (¬P) = (P → False) := rfl

example (P : Prop) (hP : P) (hnP : ¬P) : False :=
  hnP hP
```

## `True` and `False`
%%%
tag := "false-true-types"
number := false
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
number := false
%%%

`P ∧ Q` is notation for `And P Q`, the {ref "structures"}[structure] with two proof fields from the previous chapter.

*Formation.* `P ∧ Q`. *Construction.* `⟨hP, hQ⟩`, short for `And.intro hP hQ`. *Use.* The projections `h.1` and `h.2`, also `h.left` and `h.right`. *Computation.* `⟨hP, hQ⟩.1` reduces to `hP`. It is the product `α × β`, for propositions.

## Disjunction
%%%
tag := "disjunction-sum"
number := false
%%%

`P ∨ Q` is notation for `Or P Q`, the inductive type with two constructors from the {ref "inductive"}[previous chapter].

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
number := false
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
number := false
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

The last way to form a type, after universes, function types and inductive types, is the *quotient*. Given a type `α` and a relation `r : α → α → Prop`, the type `Quot r` glues together elements that `r` relates: `α` seen up to `r`. This makes `ℝ` as Cauchy sequences up to equivalence an actual construction ({ref "reals-quotient"}[below]). `Multiset α` (lists up to reordering) is a quotient in Mathlib. ℤ, ℚ and ℤ/nℤ are quotients in mathematics, but Lean defines them through normal forms instead: `Int` is an inductive type with the constructors `ofNat n` and `negSucc n` (for `-(n + 1)`), `Rat` is a structure of a numerator and a denominator with proofs that the fraction is reduced, and `ZMod n` is `Fin n` for `n > 0`.

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

## Example: the integers mod n
%%%
tag := "zmod-quotient"
number := false
%%%

ℤ/nℤ, which appeared as `ZMod n` in {ref "pi-types"}[Dependent functions], is the quotient of ℤ by the relation "same remainder mod `n`". Built by hand:

```lean
-- a and b have the same remainder mod n
def ModRel (n a b : ℤ) : Prop := a % n = b % n

def IntMod (n : ℤ) : Type := Quot (ModRel n)

def IntMod.mk (n a : ℤ) : IntMod n :=
  Quot.mk (ModRel n) a

example : IntMod.mk 5 7 = IntMod.mk 5 2 :=
  Quot.sound rfl
```

`Quot.sound` turns the proof `7 % 5 = 2 % 5`, which is `rfl`, into the equality of the two classes. A function out of `IntMod n` needs a proof that it is well defined. For the remainder of a class this proof is the relation itself:

```lean
def IntMod.rem (n : ℤ) : IntMod n → ℤ :=
  Quot.lift (fun a => a % n) (fun _ _ h => h)

example : IntMod.rem 5 (IntMod.mk 5 17) = 2 := rfl
```

The map to Mathlib's `ZMod n` sends the class of `a` to `a` read in `ZMod n`. It is well defined by the library theorem `ZMod.intCast_eq_intCast_iff'`, which says that two integers are equal in `ZMod n` exactly when they have the same remainder:

```lean
def IntMod.toZMod (n : ℕ) : IntMod n → ZMod n :=
  Quot.lift (fun a => (a : ZMod n))
    (fun a b h =>
      (ZMod.intCast_eq_intCast_iff' a b n).mpr h)
```

Mathlib itself does not define `ZMod n` as a quotient. It defines it by pattern matching on `n`, as `ℤ` for `n = 0` and as `Fin n` otherwise, which makes it computable: `#eval` and `decide` work on it. `ZMod n` is still isomorphic to the quotient of ℤ by the ideal `nℤ`; see {ref "quotients"}[Quotient structures] in chapter 2.5 for reference.

## Example: the real numbers
%%%
tag := "reals-quotient"
number := false
%%%

In analysis, `ℝ` is the completion of `ℚ`: a real number is given by a Cauchy sequence of rationals, and two Cauchy sequences give the same real number if their difference tends to `0`. Mathlib builds `ℝ` in exactly this way, in three steps, each a type former of this chapter or the previous one.

*Cauchy sequences: a subtype.* `CauSeq ℚ abs` is `{f : ℕ → ℚ // IsCauSeq abs f}`, a sequence of rationals together with a proof that it is Cauchy for the absolute value `abs`.

```lean
#check (CauSeq ℚ abs)
example (f : CauSeq ℚ abs) : ℕ → ℚ := f.1
```

*Classes of sequences: a quotient.* Two Cauchy sequences are related, `f ≈ g`, if `f - g` tends to `0`. The quotient by this relation is `CauSeq.Completion.Cauchy abs`, and `CauSeq.Completion.mk` is its `Quot.mk`. Related sequences give the same class by `Quotient.sound`, the form of `Quot.sound` for an equivalence relation:

```lean
example (f g : CauSeq ℚ abs) :
    f ≈ g ↔ (f - g).LimZero := Iff.rfl

example : CauSeq.Completion.Cauchy (abs : ℚ → ℚ) =
    Quotient (CauSeq.equiv (abv := (abs : ℚ → ℚ))) := rfl

example (f g : CauSeq ℚ abs) (h : f ≈ g) :
    CauSeq.Completion.mk f = CauSeq.Completion.mk g :=
  Quotient.sound h
```

*The real numbers: a structure.* `ℝ` is a {ref "structures"}[structure] with one field, an element of this quotient. The wrapper makes Lean treat `ℝ` as a type of its own instead of unfolding it to the quotient.

```lean
#print Real
-- structure Real : Type
--   Real.cauchy : CauSeq.Completion.Cauchy abs
```

*Operations: well-definedness.* Two real numbers are added by adding representative sequences termwise. This is well defined because addition respects the relation: `f ≈ f'` and `g ≈ g'` give `f + g ≈ f' + g'`. With that proved, `Quot.lift` gives addition on the classes, and its computation rule says that `mk` turns the sum of sequences into the sum of reals:

```lean
example (f g : CauSeq ℚ abs) :
    CauSeq.Completion.mk f + CauSeq.Completion.mk g
      = CauSeq.Completion.mk (f + g) :=
  CauSeq.Completion.mk_add f g
```

This equation is the computation step `Quot.lift f h (Quot.mk r a) ⟶ f a`, for an operation with two arguments. Multiplication, the order and the limits of `ℝ` are defined in the same way: on representatives, with a proof that the result does not depend on the choice.

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

# Some history
%%%
tag := "types-history"
%%%

Types were introduced to stop a contradiction. Russell's set $`R = \{x : x \notin x\}` broke Frege's *Grundgesetze der Arithmetik* in 1902 ({ref "prehistory"}[Introduction]). Russell's repair of 1908 gave every object a type and let a type apply only to objects of lower type, so that `x ∈ x` is not false but not a statement at all. Zermelo's repair of the same year instead restricts which sets exist and leaves `x ∈ x` a formula. Mathematics followed Zermelo; proof assistants follow Russell, because a type checker can decide before any question of truth whether an expression means anything.

*Principia Mathematica* (1910 to 1913) is written in Russell's theory. Leon Chwistek and Frank Ramsey simplified it in the 1920s to the simple theory of types, and Alonzo Church turned that into a calculus in 1940, the simply typed lambda calculus on which *Isabelle/HOL* still rests. That propositions can be read as types and proofs as terms is the *Curry-Howard correspondence*: Haskell Curry observed in 1934 that the types of the combinators of combinatory logic are the axioms of propositional logic, and William Howard extended this in 1969 (published 1980) to natural deduction and the simply typed lambda calculus. Dependent types, in which a type may mention a term, came with de Bruijn's Automath (1967) and Martin-Löf's type theory (1971). Coquand and Huet added impredicative quantification in the Calculus of Constructions (1985), and Paulin-Mohring added inductive types (1990). Lean's type theory is a variant of the result, the {ref "cic"}[Calculus of Inductive Constructions]. Three times the same thing happened: a system let an object be applied to itself, a contradiction followed, and types forbade it. In Lean the ban is visible as `Type 0 : Type 1 : Type 2 : ...`.
