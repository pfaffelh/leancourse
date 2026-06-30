import VersoManual
import Manual.Meta
import Mathlib

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

set_option pp.rawOnError true

#doc (Manual) "Well-Foundedness and Paradoxes" =>
%%%
htmlSplit := .never
tag := "logic-wf"
%%%

A recurring worry in the foundations of mathematics is *vicious
circularity*: infinite descending chains that make recursion
meaningless, or self-referential sets like Russell's `{x | x ∉ x}`.
Lean rules these out, but -- importantly -- by *two different
mechanisms* that are worth keeping apart.  This short chapter looks at
both.

# Accessibility and well-founded relations
%%%
tag := "wf-acc"
%%%

The first mechanism lives *inside* a type and governs recursion.  A
relation `r : α → α → Prop` is *well-founded* when there are no
infinite descending chains `… r a₂ r a₁ r a₀`.  Lean expresses this
through the inductive predicate `Acc` ("accessible"):

```
inductive Acc (r : α → α → Prop) : α → Prop where
  | intro (x : α) (h : ∀ y, r y x → Acc r y) : Acc r x
```

Read the constructor as: `x` is *accessible* once *all* of its
`r`-predecessors `y` (those with `r y x`) are themselves accessible.
A relation is well-founded when every element is accessible:

```lean
#check @Acc
-- Acc : {α : Sort u} → (α → α → Prop) → α → Prop
#check @WellFounded
-- WellFounded : {α : Sort u} → (α → α → Prop) → Prop
#check @WellFounded.fix
```

The crucial observation is that `Acc` is an *inductive* type -- the
*least* fixed point, so it is finitely generated.  A proof of `Acc r
x` is therefore a *finite* tree of predecessors; an infinite
descending chain would require an infinitely deep proof, which no
inductive type admits.  This is exactly what powers *well-founded
recursion* (`WellFounded.fix`): you may recurse along `r` because
every descent terminates.  The `termination_by` and `decreasing_by`
clauses use precisely this.

# Why `Nat` is well-founded
%%%
tag := "wf-nat"
%%%

The relation `<` on `Nat` is well-founded:

```lean
#check (Nat.lt_wfRel.wf : WellFounded Nat.lt)
```

One proves `Acc (· < ·) n` by induction on `n`:

- `0` is accessible *vacuously* -- there is no `m < 0`.
- `n + 1` is accessible because every `m < n + 1` (that is, `m ≤ n`)
  is accessible by the induction hypothesis.

The deeper reason is that `Nat` is *itself* an inductive type
(`zero | succ`): every natural number is a *finite* tower of `succ`
over `zero`, so there is no infinite natural number to descend
through.  Structural recursion on `Nat` is the prototype of
well-founded recursion, and the well-foundedness of `<` is just a
restatement of it.

# Why `s ∈ s` is impossible
%%%
tag := "wf-membership"
%%%

The second mechanism is *typing*, and it is what blocks
self-membership and Russell's paradox.  Unlike ZFC, Lean has no global
membership relation: `∈` is *typed*.  The instance behind it,

```lean
#check @Set.instMembership
-- Membership α (Set α)
```

says that `x ∈ s` requires `x : α` and `s : Set α`.  For `s ∈ s` the
same `s` would need type `α` *and* type `Set α` at once -- that is,
`α = Set α`, i.e. `α = (α → Prop)`.  No such type exists (there is no
matching `Membership` instance, and by *Cantor's theorem*
`α ≄ (α → Prop)`).  So `s ∈ s` is not a *false* statement; it is
*ill-formed*:

```lean
def mySet : Set ℕ := {0}

-- `#check_failure` succeeds exactly because the term
-- below fails to elaborate -- `mySet ∈ mySet` is a type
-- error, not a refutable proposition.
#check_failure (mySet ∈ mySet)
```

Consequently Russell's set `{x | x ∉ x}` cannot even be *written* in
Lean.  Compare ZFC (see {ref "comparison-zfc"}[the ZFC comparison]),
where `s ∈ s` *is* a well-formed proposition and is excluded only by
the separate axiom of foundation.  Lean rules it out one step
earlier, by typing.

# The universe hierarchy and `Type : Type`
%%%
tag := "wf-universes"
%%%

The same typing discipline, one level up, forbids `Type : Type`.  If
`Type` contained itself, Girard's paradox (a type-theoretic Russell)
would make every proposition provable.  The
{ref "universe-hierarchy"}[universe hierarchy] prevents it:
`Type : Type 1`,
`Type 1 : Type 2`, and so on, but never `Type : Type`.

```lean
#check (Type : Type 1)         -- fine
#check_failure (Type : Type)   -- forbidden
```

# Two kinds of "no vicious circle"
%%%
tag := "wf-summary"
%%%

It is worth holding the two mechanisms apart -- they forbid
circularity at different places:

:::table +header
* + Phenomenon ruled out
  + Mechanism
* + Infinite descent; non-terminating recursion
  + `Acc` / `WellFounded` -- an inductive predicate *within* a type
* + `s ∈ s`, `{x | x ∉ x}`, `Type : Type`
  + Typing and the universe hierarchy -- the *structure* of the system
:::

Both express the intuition "no self-swallowing circles", but the first
is a *theorem-level* tool you invoke for recursion, while the second
is baked into the *well-formedness* rules of the language.
