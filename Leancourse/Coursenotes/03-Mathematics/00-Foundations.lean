import VersoManual
import Manual.Meta
import Leancourse.Misc.Defs
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

A mathematician thinks in *sets*; Lean thinks in *types*. This chapter
pins down how the two relate -- how a set is represented, how its
operations unfold to familiar logical connectives, how set equality
works, and how sets, subtypes, and types differ. The other staple that
every later chapter takes for granted -- *propositions* and their
*proofs* -- was covered in {ref "curry-howard"}[the Curry-Howard
chapter] of the {ref "lean"}[Lean part]; from here on we use it freely.

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
:::

# Sets are predicates
%%%
tag := "foundations-sets"
%%%

In Mathlib a set over a type `α` has type `Set α`, and `Set α` is
*definitionally* the function type `α → Prop`.  A set is thus nothing
more than a predicate: the term `a : α` belongs to `s : Set α` exactly
when `s a` holds, and `a ∈ s` is notation for precisely that.

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

This `α → Prop` definition is why
{ref "axiom-propext"}[propositional extensionality] matters in
everyday mathematics: it is what lets two predicates that are
logically equivalent count as the *same* set.

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

# Set equality and the axioms
%%%
tag := "foundations-set-eq"
%%%

Two sets are equal exactly when they have the same members.  This is
the *set extensionality* principle `Set.ext`, and it is where the
foundations of the previous part pay off: a set is a function into
`Prop`, so "same members" gives equality through
{ref "axiom-funext"}[function extensionality] and
{ref "axiom-propext"}[propositional extensionality].

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

# Sets, subtypes, and types
%%%
tag := "foundations-sets-subtypes"
%%%

It is worth keeping three closely related notions apart.

- A *type* `α` is the ambient collection of terms.
- A *set* `s : Set α` is a predicate carving out some terms of `α`;
  crucially, its elements still have type `α`.
- A *subtype* `{ x : α // p x }` (see
  {ref "subtypes"}[Subtypes]) is a brand-new type whose terms are
  pairs of a value and a proof that it satisfies `p`.

A set can be *promoted* to a type by coercion: `↥s` denotes the
subtype `{ x // x ∈ s }` of its members.  This is how a set becomes a
type in its own right -- for instance when we want to speak of a
function defined only on `s`.

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
