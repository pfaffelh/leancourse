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
infinite descending chains `… r a₂ r a₁ r a₀` -- following
`r`-predecessors downward, you always hit bottom after finitely many
steps.

Why care?  Well-foundedness is *exactly* the condition that makes
recursion and induction legitimate.  If `f x` is defined in terms of
`f y` for `r`-smaller `y`, the computation terminates *only* because
you cannot descend forever; and the induction principle "to prove
`P x`, assume `P y` for every `y` with `r y x`" is valid *precisely*
when `r` is well-founded.  In one phrase: well-founded means "you may
recurse and induct along `r`".

Lean expresses this through the inductive predicate `Acc`
("accessible"):

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
*least* fixed point, so it is finitely generated.  The constructor
for `Acc r x` demands accessibility of *every* predecessor, so the
only way to build the proof is for every downward branch to bottom
out after finitely many steps: a proof of `Acc r x` is a *finite*
tree.  An infinite descending chain would force an infinitely deep
proof, which no inductive type admits -- so, where every element is
accessible, no such chain exists.  (Were `Acc` instead *coinductive*,
the *greatest* fixed point, infinite proofs would be allowed and
every element would count as accessible; the definition would be
vacuous.  The induction is the whole point.)  This is exactly what
powers *well-founded recursion* (`WellFounded.fix`): you may recurse
along `r` because every descent terminates, and `termination_by` /
`decreasing_by` use precisely this.

It helps to see what *fails*.  These relations are *not*
well-founded:

- `<` on the integers `ℤ`: the chain `0 > -1 > -2 > …` descends
  forever, with no bottom.
- `<` on `ℚ` or `ℝ`: `1 > ½ > ¼ > …` never terminates.
- *greater-than* `>` on `ℕ`: the chain `0 < 1 < 2 < …` is an infinite
  `>`-descending chain.

For none of these can Lean offer well-founded recursion -- there is no
terminating direction to recurse in.  The contrast between `<` and `>`
on `ℕ` is the lesson: less-than bottoms out at `0`, greater-than runs
off to infinity.

Concretely, this abstract picture is realized in Lean in two ways.
Each `inductive` type comes with an auto-generated *recursor*
(`Nat.rec`, `List.rec`, ...) that *is* its structural induction and
recursion principle -- well-foundedness for that type, guaranteed by
the kernel.  And for a *uniform* supply of well-founded relations,
every inductive type carries a `SizeOf` instance, which `sizeOfWFRel`
turns into a `WellFoundedRelation` whose well-foundedness is pulled
back from `<` on `Nat` through `InvImage.wf`.  So "inductive, hence
finite trees, hence well-founded" becomes, in practice, the single
fact `Nat.lt_wfRel.wf` transported along `sizeOf`.

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

In practice you almost never prove well-foundedness yourself.  Mathlib
already supplies it -- the `Nat.lt_wfRel.wf` above is one of many
`WellFoundedRelation` instances -- and when you write a recursive
definition with `termination_by` (next section), Lean finds the
well-founded relation automatically and asks you only, via
`decreasing_by`, to show that your *measure* decreases.  The induction
argument just given is the one-time justification the library
performs, not something you repeat; you would do it by hand only for a
genuinely new, exotic relation.

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

A word on the *Cantor's theorem* invoked above.  It states that for
any type `α` there is no surjection `α → Set α`: the type of subsets
`Set α = α → Prop` is always *strictly larger* than `α` itself
(Mathlib's `Function.cantor_surjective`).  In particular `α` and
`α → Prop` can never be the *same* type, which is exactly what rules
out `α = Set α`.  The proof is a *diagonal argument*: given any
candidate surjection `f : α → Set α`, the "diagonal" subset
`{x | x ∉ f x}` is hit by no `f x` at all -- if `f a` were equal to
it, then `a ∈ f a` and `a ∉ f a` would coincide.  That diagonal subset
is *precisely* Russell's `{x | x ∉ x}`: Cantor's theorem and Russell's
paradox are the same construction, with Cantor drawing the consistent
conclusion (no such surjection exists) exactly where naive set theory
runs into a contradiction.

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
