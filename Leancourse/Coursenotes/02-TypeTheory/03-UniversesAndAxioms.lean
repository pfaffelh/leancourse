import VersoManual
import Manual.Meta
import Leancourse.Misc.Defs
import Mathlib

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open MyDef

set_option pp.rawOnError true

#doc (Manual) "Universes, Axioms, and Foundations" =>
%%%
htmlSplit := .never
tag := "universes-axioms"
%%%

Lean's type theory rests on a carefully designed system of universes, a small number of axioms, and a powerful logic that can be used both constructively and classically. In this chapter, we examine these foundational aspects.

# The universe hierarchy
%%%
tag := "universe-hierarchy"
%%%

In Lean, every type itself has a type. To avoid paradoxes (like Russell's paradox), types are organized into a hierarchy of **universes**:

- `Prop` is the universe of propositions. It is also called `Sort 0`.
- `Type 0` (or simply `Type`) is the universe of "ordinary" types. It is also called `Sort 1`.
- `Type 1` is the universe of types whose elements are themselves types in `Type 0`. It is `Sort 2`.
- In general, `Type n` is `Sort (n + 1)`.

The key rule is that `Sort n : Sort (n + 1)`, so:

```lean
#check (Prop : Type 0)      -- Prop : Type
#check (Type 0 : Type 1)    -- Type : Type 1
#check (Type 1 : Type 2)    -- Type 1 : Type 2
```

This hierarchy prevents `Type : Type`, which would lead to Girard's paradox (a type-theoretic analogue of Russell's paradox).

# Prop vs Type: proof irrelevance
%%%
tag := "prop-vs-type"
%%%

The universe `Prop` has a special property that distinguishes it from all `Type n`: **proof irrelevance**. This means that if `P : Prop` and `h1 h2 : P`, then `h1 = h2`. In other words, all proofs of the same proposition are considered equal.

This is a deliberate design choice. It means:
- You cannot pattern-match on a proof to extract computational data.
- Proofs can be erased at compile time without affecting program behavior.
- Two mathematical proofs of the same theorem are interchangeable.

```lean
-- Proof irrelevance: any two proofs of the same Prop are equal
example (P : Prop) (h1 h2 : P) : h1 = h2 :=
  rfl

-- This is why ∃ lives in Prop: you cannot extract the witness computationally
-- If you need the witness, use Σ (which lives in Type)
```

The distinction between `Prop` and `Type` corresponds to the mathematical distinction between "asserting that something exists" (Prop) and "constructing a specific example" (Type).

# Universe polymorphism
%%%
tag := "universe-polymorphism"
%%%

Many definitions in Lean need to work across multiple universe levels. For this, Lean supports **universe polymorphism**. You can declare universe variables and use them in definitions:

```lean
universe u v

-- A universe-polymorphic identity function
def myId' (α : Type u) (a : α) : α := a

-- Works at any universe level
#check myId' ℕ 42           -- ℕ
#check myId' (Type 0) ℕ     -- Type
```

In Mathlib, many definitions are universe-polymorphic. For example, `Set α` works regardless of which universe `α` lives in. When you see `{α : Type*}`, the `*` means "at any universe level" -- this is Lean's way of automatically introducing a universe variable.

# The axioms of Lean
%%%
tag := "lean-axioms"
%%%

Lean's kernel is built on the Calculus of Inductive Constructions, which by itself is quite weak. To support the mathematics we want to formalize, Lean adds a small number of axioms. Let us examine each one.

## Function extensionality (`funext`)
%%%
tag := "axiom-funext"
%%%

Two functions are equal if and only if they give the same output on every input. This is the axiom `funext`:

```lean
-- funext: if f x = g x for all x, then f = g
#check @funext
-- funext : ∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x},
--   (∀ (x : α), f x = g x) → f = g

example : (fun n : ℕ => n + 0) = (fun n : ℕ => n) := by
  funext n
  simp
```

Without `funext`, we could not prove that two functions are equal, even if they demonstrably agree everywhere. This axiom is indispensable in mathematics.

## Propositional extensionality (`propext`)
%%%
tag := "axiom-propext"
%%%

Two propositions are equal if and only if they are logically equivalent:

```lean
#check @propext
-- propext : ∀ {a b : Prop}, (a ↔ b) → a = b

-- Example: P ∧ True is the same proposition as P
example (P : Prop) : (P ∧ True) = P := by
  ext
  simp
```

This axiom is essential for working with sets (since `Set α` is defined as `α → Prop`, and we want equal predicates to give equal sets).

## The axiom of quotients
%%%
tag := "axiom-quot"
%%%

Lean has built-in support for quotient types. Given a type `α` and an equivalence relation `r` on `α`, you can form the quotient type `Quot r`. The axiom `Quot.sound` says that if `r a b`, then `Quot.mk r a = Quot.mk r b`.

This is how many mathematical constructions are formalized: the integers as a quotient of `ℕ × ℕ`, the rationals as a quotient of `ℤ × ℤ`, the reals as a quotient of Cauchy sequences, and so on.

```lean
-- Quotient types are built into Lean
#check @Quot.mk
#check @Quot.sound
#check @Quot.lift
```

## The axiom of choice (`Classical.choice`)
%%%
tag := "axiom-choice"
%%%

The most powerful (and most controversial) axiom in Lean is the axiom of choice:

```lean
#check @Classical.choice
-- Classical.choice : ∀ {α : Sort u}, Nonempty α → α
```

Given a proof that a type is nonempty (i.e., inhabited), `Classical.choice` produces an actual element. This is a non-constructive axiom: it asserts existence without providing a construction.

From this single axiom (together with `propext` and `Quot.sound`), one can derive:
- The law of excluded middle: `∀ (P : Prop), P ∨ ¬P`
- The axiom of choice in its more familiar set-theoretic form
- Hilbert's epsilon operator

# Constructive vs classical logic
%%%
tag := "constructive-classical"
%%%

By default, Lean's type theory is **constructive**: proofs must provide explicit witnesses and constructions. The axiom of choice introduces **classical** reasoning, which allows non-constructive arguments.

## Excluded middle
%%%
tag := "excluded-middle"
%%%

In classical logic, every proposition is either true or false. This is expressed by the **law of excluded middle**:

```lean
#check @Classical.em
-- Classical.em : ∀ (p : Prop), p ∨ ¬p

-- With excluded middle, we can do case splits on any proposition
example (P : Prop) : ¬¬P → P := by
  intro hnnP
  by_contra hnP
  exact hnnP hnP
```

Without `Classical.em`, double negation elimination `¬¬P → P` is not provable. This is one of the key differences between constructive and classical logic.

## The Decidable typeclass
%%%
tag := "decidable-typeclass"
%%%

Lean has a clever middle ground between constructive and classical logic: the `Decidable` typeclass. A proposition `P` is `Decidable` if there is an algorithm that determines whether `P` is true or false.

```lean
-- Decidable means we can compute the truth value
#check @Decidable
-- Decidable : Prop → Type

-- Many concrete propositions are decidable
#check (inferInstance : Decidable (2 + 3 = 5))  -- isTrue ...
#check (inferInstance : Decidable (2 + 3 = 6))  -- isFalse ...
```

When a proposition is `Decidable`, you can use `if P then ... else ...` in code without needing the axiom of choice. This is important for writing executable programs. The `decide` tactic can close goals about decidable propositions:

```lean
example : 2 + 3 = 5 := by decide
example : ¬(2 + 3 = 6) := by decide
```

When you open `Classical`, every `Prop` becomes `Decidable` (non-constructively). This is convenient for proofs but means the resulting code is not executable.

## When do you need Classical.choice?
%%%
tag := "when-classical"
%%%

You need classical axioms when:
- You want to do a case split on an arbitrary proposition (`by_cases`, `by_contra`)
- You want to choose an element from a nonempty type without a constructive witness
- You want to use the law of excluded middle

You do *not* need classical axioms when:
- Working with decidable propositions (natural number arithmetic, finite structures)
- Constructing specific terms (defining functions, data structures)
- Proving things by direct construction or induction

In Mathlib, most proofs use classical logic freely (via `open Classical`), since the focus is on mathematical truth rather than computational content.

# Comparison with ZFC set theory
%%%
tag := "comparison-zfc"
%%%

Most mathematicians are (at least implicitly) trained in ZFC set theory. Here are the key differences from Lean's type theory:

:::table +header
* + Feature
  + ZFC
  + Lean
* + Foundation
  + Sets and membership `∈`
  + Types and terms `:`
* + Everything is a...
  + Set
  + Term of some type
* + `3 ∈ 7`
  + Well-formed (and true!)
  + Type error
* + Functions
  + Sets of ordered pairs
  + Primitive notion
* + Equality
  + Between any two sets
  + Only within a type
* + Proof objects
  + Not part of the theory
  + First-class citizens
* + Computation
  + Not built in
  + Built in (terms reduce)
* + Type checking
  + Not applicable
  + Decidable (in practice)
:::

A key practical difference: in ZFC, you can ask nonsensical questions like "is 3 ∈ π?" and get an answer. In Lean, comparing objects of different types is a type error, which catches many mistakes early.

Both foundations are equiconsistent for most of mathematics. Nearly everything that can be formalized in ZFC can also be formalized in Lean's type theory (and vice versa).

# Brief mention of other type theories
%%%
tag := "other-type-theories"
%%%

Lean's type theory is one of several:

- **Simply typed lambda calculus** (Church, 1940): No dependent types. Foundation for Haskell, OCaml.
- **System F** (Girard, Reynolds, 1970s): Adds polymorphism but not full dependent types.
- **Martin-Löf Type Theory** (MLTT, 1971+): The origin of dependent types in proof assistants. Used in Agda.
- **Calculus of Inductive Constructions** (CoIC): Used in Coq/Rocq. Lean's type theory is closely related.
- **Homotopy Type Theory** (HoTT, 2013): Interprets types as topological spaces and equality as paths. Adds the univalence axiom (due to Voevodsky): equivalent types are equal. This is incompatible with Lean's proof irrelevance for `Prop`, so HoTT uses different proof assistants (Agda, cubical Agda, or specialized Lean forks).
- **Cubical Type Theory** (2015+): Makes HoTT computational by using a cube category to model paths.

For this course, Lean's type theory (CIC + proof irrelevance + quotients + choice) is the framework we work in. It is expressive enough to formalize virtually all of modern mathematics, as the Mathlib library demonstrates.
