import VersoManual
import Manual.Meta
import Leancourse.Markup
import Mathlib

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open MyDef

set_option pp.rawOnError true
set_option verso.docstring.allowMissing true

#doc (Manual) "Sets and Types" =>
%%%
htmlSplit := .never
tag := "sets-and-types"
%%%

A mathematician thinks in *sets*; Lean thinks in *types*. A set turns
out to be a predicate on a type, its operations the logical
connectives, and its equality an axiom. Functions act on sets by
image and preimage, and injectivity and surjectivity are again
formulas with quantifiers.
*Propositions* and their *proofs*, used freely from here on, were
covered in {ref "curry-howard"}[Propositions as types] in the
{ref "lean"}[Lean part].

# Sets versus types
%%%
tag := "set-vs-type"
%%%

The first reflex to unlearn is the set-theoretic one that *everything
is a set*. In set theory `∈` is the single primitive, an object can be
a member of many sets, and there is no fixed notion of "the type of
`x`". Type theory inverts this: the primitive is the *type*, and every
term `a : α` has *exactly one* type, fixed once and for all.

A set in Lean is **not** a new type. A `Set α` is a predicate on the
already-existing type `α`, carving out some of its terms. An element of
`s : Set α` therefore still has type `α`; the set records only *which*
terms of `α` lie in it.

Three notions are worth keeping firmly apart:

- a *type* `α` — the ambient collection of terms;
- a *set* `s : Set α` — a predicate selecting terms of `α`, whose
  elements *keep* their type `α`;
- a *subtype* `{ x : α // p x }` (see {ref "subtypes"}[Subtypes]) — a
  genuinely *new* type, whose terms are pairs of a value and a proof
  that it satisfies `p`.

So there *is* a difference between a set and a type, and it is the one
a mathematician must internalize. The rest of this chapter makes it
precise: sets as predicates and their operations, when two sets are
equal, and finally how to cross the gap — turning a set back into a
type.

# Notation and naming conventions
%%%
tag := "foundations-notation"
%%%

The set-theoretic symbols below are unicode characters typed in VS
Code via a backslash escape.  Hover over a symbol in the editor to see
its input sequence.

:::table +header
* + Symbol
  + Lean name
  + Reads as
  + Typed as
* + `∈`
  + `Membership.mem`
  + "is a member of"
  + `\in`
* + `∉`
  + `· ∉ ·`
  + "is not a member of"
  + `\notin`
* + `⊆`
  + `HasSubset.Subset`
  + "is a subset of"
  + `\subseteq`
* + `∪`
  + `Union.union`
  + "union"
  + `\cup`
* + `∩`
  + `Inter.inter`
  + "intersection"
  + `\cap`
* + `ᶜ`
  + `HasCompl.compl`
  + "complement"
  + `\compl`
* + `∅`
  + `EmptyCollection`
  + "the empty set"
  + `\empty`
* + `{x | p x}`
  + `setOf`
  + "the set of `x` with `p x`"
  + (literal braces)
* + `f '' s`
  + `Set.image`
  + "the image of `s` under `f`"
  + (two apostrophes)
* + `f ⁻¹' t`
  + `Set.preimage`
  + "the preimage of `t` under `f`"
  + `\inv'`
:::

# Sets are predicates
%%%
tag := "foundations-sets"
%%%

`Set α` is *definitionally* the function type `α → Prop`. The term
`a : α` belongs to `s : Set α` exactly when `s a` holds, and `a ∈ s` is
notation for that.

```lean
-- `Set α` is definitionally `α → Prop`
#check (Set ℕ)
example : Set ℕ = (ℕ → Prop) := rfl

-- Set-builder notation packages a predicate as a set
def Evens : Set ℕ := { n | n % 2 = 0 }

-- Membership unfolds to applying the predicate
example : (4 ∈ Evens) ↔ (4 % 2 = 0) := Iff.rfl

-- ...so concrete membership questions are decidable
example : 4 ∈ Evens := by
  show 4 % 2 = 0
  decide

example : 3 ∉ Evens := by
  show ¬ (3 % 2 = 0)
  decide
```

Because a set *is* a predicate, two predicates that hold of exactly
the same elements describe the *same* set — set equality is
*extensional*. We make this precise just below.

# Subset, union, intersection, complement
%%%
tag := "foundations-set-ops"
%%%

The usual Boolean operations on sets are all defined pointwise on the
underlying predicates, so each unfolds to a familiar logical
connective.

```lean
-- `s ⊆ t` means: every member of `s` is a member of `t`
example (s t : Set ℕ) :
    (s ⊆ t) ↔ ∀ a, a ∈ s → a ∈ t := Iff.rfl

-- the empty set, the universal set, and the operations
#check (∅ : Set ℕ)
#check (Set.univ : Set ℕ)
example (s t : Set ℕ) : Set ℕ := s ∩ t   -- intersection
example (s t : Set ℕ) : Set ℕ := s ∪ t   -- union
example (s : Set ℕ)   : Set ℕ := sᶜ      -- complement
```

# Indexed unions and intersections
%%%
tag := "foundations-indexed-ops"
%%%

The binary `∪` and `∩` extend to *arbitrary* families. Given `s : ι → Set α` — a set `s i` for each index `i : ι` — the *indexed union* `⋃ i, s i` and *indexed intersection* `⋂ i, s i` collect members across the whole family.

{docstring Set.iUnion}

{docstring Set.iInter}

As always, membership just unfolds to a quantifier:

```lean
-- `a ∈ ⋃ i, s i` iff `a` lies in *some* member of the family
example (s : ℕ → Set ℕ) (a : ℕ) :
    (a ∈ ⋃ i, s i) ↔ ∃ i, a ∈ s i := Set.mem_iUnion

-- `a ∈ ⋂ i, s i` iff `a` lies in *every* member
example (s : ℕ → Set ℕ) (a : ℕ) :
    (a ∈ ⋂ i, s i) ↔ ∀ i, a ∈ s i := Set.mem_iInter

-- a concrete union: the singletons cover all of `ℕ`
example : (⋃ n : ℕ, {n}) = Set.univ := by
  ext a; simp
```

A common variant restricts the index to a *set* `a : Set ι` rather than the whole index type — written `⋃ i ∈ a, s i` and `⋂ i ∈ a, s i`. This is just the indexed operation ranging over the members of `a`, and membership carries the bound along:

```lean
-- union over `i` ranging in a set `a`
example (a : Set ℕ) (s : ℕ → Set ℕ) (x : ℕ) :
    (x ∈ ⋃ i ∈ a, s i) ↔ ∃ i ∈ a, x ∈ s i := by
  simp only [Set.mem_iUnion, exists_prop]

-- and the bounded intersection
example (a : Set ℕ) (s : ℕ → Set ℕ) (x : ℕ) :
    (x ∈ ⋂ i ∈ a, s i) ↔ ∀ i ∈ a, x ∈ s i := by
  simp only [Set.mem_iInter]
```

When the family is given not by an index but as a *set of sets* `S : Set (Set α)`, the same operations are written `⋃₀ S` (`sUnion`) and `⋂₀ S` (`sInter`):

{docstring Set.sUnion}

{docstring Set.sInter}

```lean
-- `a ∈ ⋃₀ S` iff `a` lies in some `t ∈ S`
example (S : Set (Set ℕ)) (a : ℕ) :
    (a ∈ ⋃₀ S) ↔ ∃ t ∈ S, a ∈ t := Set.mem_sUnion
```

These are exactly the set/indexed suprema and infima of the {ref "complete-lattices"}[complete lattice of sets]: `⋃ i, s i` *is* `iSup s`, and `⋃₀ S` *is* `sSup S`. They are also what {ref "measurable-space"}[σ-algebras] are closed under — a *countable* union or intersection is just the indexed one over `ι = ℕ`.

# Set equality
%%%
tag := "foundations-set-eq"
%%%

Two sets are equal exactly when they have the same members: the *set
extensionality* principle `Set.ext`. This is not a definition but a
consequence of the axioms — a set is a function into `Prop`, so it
rests on the extensionality axioms taken up in
the next chapter. Here we simply use it.

```lean
-- equality of sets is membership-wise equality
example (s t : Set ℕ) :
    s = t ↔ ∀ a, a ∈ s ↔ a ∈ t :=
  ⟨fun h a => by rw [h], fun h => Set.ext h⟩

-- the `ext` tactic reduces a set equality to membership
example : { n : ℕ | n % 2 = 0 } = { n | 2 ∣ n } := by
  ext n
  simp only [Set.mem_setOf_eq]
  constructor <;> intro h <;> omega
```

# Image and preimage
%%%
tag := "image-preimage"
%%%

For `f : α → β`, `s : Set α` and `t : Set β`, the *image* `f '' s`
is the set of all `f x` with `x ∈ s`, and the *preimage* `f ⁻¹' t` is
the set of all `x` with `f x ∈ t`. Membership unfolds differently in
the two cases: in the image it is an existential, in the preimage a
statement about the value `f x`.

```lean
example (f : ℕ → ℕ) (s : Set ℕ) (y : ℕ) :
    y ∈ f '' s ↔ ∃ x, x ∈ s ∧ f x = y := Iff.rfl

example (f : ℕ → ℕ) (t : Set ℕ) (x : ℕ) :
    x ∈ f ⁻¹' t ↔ f x ∈ t := Iff.rfl

example : (fun n : ℕ => n % 2) ⁻¹' {0}
    = {n | n % 2 = 0} := rfl
```

So a hypothesis `h : y ∈ f '' s` is a triple: `obtain ⟨x, hx, rfl⟩ :=
h` gives a point `x`, a proof of `x ∈ s`, and replaces `y` by `f x`.
To prove `y ∈ f '' s` you name the point: `⟨x, hx, rfl⟩`, or `use x`.
A hypothesis `x ∈ f ⁻¹' t` needs no unpacking, it already *is*
`f x ∈ t`. The image of the whole type has its own name, `Set.range f`.

The basic fact relating the two: `f '' s ⊆ t` holds exactly when
`s ⊆ f ⁻¹' t`.

```lean
example {α β : Type*} (f : α → β) (s : Set α)
    (t : Set β) : f '' s ⊆ t ↔ s ⊆ f ⁻¹' t := by
  constructor
  · intro h x hx
    exact h ⟨x, hx, rfl⟩
  · rintro h y ⟨x, hx, rfl⟩
    exact h hx
```

The preimage commutes with all set operations, and the equalities are
`rfl`, because both sides unfold to the same predicate. The image
commutes with unions, but for intersections only `⊆` holds in general:

```lean
example {α β : Type*} (f : α → β) (t₁ t₂ : Set β) :
    f ⁻¹' (t₁ ∩ t₂) = f ⁻¹' t₁ ∩ f ⁻¹' t₂ := rfl

example {α β : Type*} (f : α → β) (s₁ s₂ : Set α) :
    f '' (s₁ ∩ s₂) ⊆ f '' s₁ ∩ f '' s₂ :=
  Set.image_inter_subset f s₁ s₂
```

# Injective and surjective functions
%%%
tag := "injective-surjective"
%%%

`Function.Injective f` and `Function.Surjective f` are the formulas
from the first semester. They are definitions, so `Iff.rfl` proves
that they say what they say; `intro` unfolds them in a proof.

```lean
open Function

example {α β : Type*} (f : α → β) :
    Injective f ↔ ∀ a b, f a = f b → a = b :=
  Iff.rfl

example {α β : Type*} (f : α → β) :
    Surjective f ↔ ∀ b, ∃ a, f a = b := Iff.rfl

example : Injective (fun n : ℕ => n + 1) := by
  intro a b h
  simpa using h

example : ¬ Surjective (fun n : ℕ => n + 1) := by
  intro h
  obtain ⟨a, ha⟩ := h 0
  simp at ha
```

In `Injective` the two points are implicit (`∀ ⦃a₁ a₂⦄`), so for
`hf : Injective f` and `h : f a = f b` one writes `hf h : a = b`. The
composition of injective maps is injective, and the proof is just
that:

```lean
open Function in
example {α β γ : Type*} {f : α → β} {g : β → γ}
    (hf : Injective f) (hg : Injective g) :
    Injective (g ∘ f) :=
  fun _ _ h => hf (hg h)
```

Both notions connect to images. `f` is surjective exactly when its
range is everything, and an injective map commutes with intersections:

```lean
open Function in
example {α β : Type*} (f : α → β) :
    Surjective f ↔ Set.range f = Set.univ :=
  Set.range_eq_univ.symm

open Function in
example {α β : Type*} {f : α → β}
    (hf : Injective f) (s₁ s₂ : Set α) :
    f '' (s₁ ∩ s₂) = f '' s₁ ∩ f '' s₂ :=
  Set.image_inter hf
```

`Bijective f` is `Injective f ∧ Surjective f`. A bijection is a
property of `f`; the inverse map is data. Mathlib packages a map
together with its inverse as `α ≃ β` (an *equivalence*), and
`Equiv.ofBijective f hf` turns a bijective `f` into one. The inverse
is then chosen by `Classical.choice`, so `Equiv.ofBijective` is
`noncomputable`.

# From a set back to a type: subtypes and coercion
%%%
tag := "foundations-sets-subtypes"
%%%

A set is not a type, and sometimes you need one: to speak of a function
defined only on `s`, or to sum over its elements. A set is *promoted*
to a type by coercion: `↥s` denotes the subtype
`{ x // x ∈ s }` of its members, a genuinely new type whose terms pair
an element of `α` with a proof of membership.

```lean
-- coercing a set to a type gives the subtype of members
#check (↥Evens)                              -- a Type
example : ↥Evens = { x : ℕ // x ∈ Evens } :=
  rfl

-- an element of the subtype pairs a value with a proof
example : ↥Evens :=
  ⟨4, by show 4 % 2 = 0; decide⟩
```

With sets, subtypes, and their relationship to types in hand, we are
ready to look at the structures Mathlib builds on top of them.
