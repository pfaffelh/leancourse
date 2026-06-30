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

# Well-founded recursion in practice: `termination_by`
%%%
tag := "wf-termination"
%%%

Lean accepts *structural* recursion automatically -- the kind where
each recursive call is on a syntactic subterm of an argument.  When a
recursive call is *not* on a subterm, you justify termination by
giving a *measure* that strictly decreases along a well-founded
relation.  The `termination_by` clause names the measure, and
`decreasing_by` discharges the proof that it goes down.

Euclid's algorithm is the classic example.  Here `euclidGcd m n`
recurses on `n % m`, which is not a subterm of `m`; but the first
argument strictly decreases, and `<` on `Nat` is well-founded (the
previous section):

```lean
def euclidGcd (m n : Nat) : Nat :=
  if _h : m = 0 then n
  else euclidGcd (n % m) m
termination_by m
decreasing_by
  exact Nat.mod_lt n (Nat.pos_of_ne_zero _h)

#eval euclidGcd 48 36   -- 12
```

Reading it off:

- `termination_by m` declares the measure to be the first argument
  `m`.
- For the recursive call `euclidGcd (n % m) m`, Lean asks you to show
  the measure shrinks -- that is, `n % m < m`.  That inequality is the
  goal handed to `decreasing_by`.
- `Nat.mod_lt n (Nat.pos_of_ne_zero _h)` proves `n % m < m` from
  `m ≠ 0`.  The hypothesis `_h : m = 0` is false in this branch and is
  in scope thanks to the dependent `if`; the underscore just tells the
  unused-variable linter that we use it only inside the proof.
- Under the hood Lean compiles this to `WellFounded.fix` over the
  well-founded relation `<` on `Nat` -- the `Acc` machinery from the
  start of the chapter.

When the decrease is routine, `decreasing_by` can often close it with
`omega`:

```lean
def log2 (n : Nat) : Nat :=
  if _h : 2 ≤ n then 1 + log2 (n / 2) else 0
termination_by n
decreasing_by omega

#eval log2 16   -- 4
```

Here the goal `n / 2 < n` follows from `2 ≤ n`, which `omega` finds on
its own.

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
