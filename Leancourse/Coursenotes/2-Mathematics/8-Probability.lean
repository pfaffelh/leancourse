import VersoManual
import Manual.Meta
import Leancourse.Markup
import Mathlib

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open MyDef
open scoped ENNReal Topology

set_option pp.rawOnError true
set_option verso.docstring.allowMissing true

#doc (Manual) "Monads and Probability Mass Functions" =>
%%%
htmlSplit := .never
tag := "probability-pmf"
%%%

`PMF α` is Mathlib's type of discrete probability distributions on `α`. It is a monad in the sense of chapter {ref "type-constructor-classes"}[1.7], and the monad structure is how one builds distributions from others. The chapter first collects the `map` and `bind` operations that have already appeared for sets, finite sets and filters.

The [slides](slides/2-8-probability/) for this chapter follow it section by section.

# Monads in mathematics
%%%
tag := "monads"
%%%

Chapter {ref "type-constructor-classes"}[1.7] introduced `map`, `pure` and `bind` for `Option` and `List`. The same three operations occur in mathematics, and so far they have appeared under other names:

:::table (align := left) +header
* + type
  + `pure a`
  + `map f`
  + `bind s f`
* + `Set α`
  + `{a}`
  + the image `f '' s`
  + the union `⋃ a ∈ s, f a`
* + `Finset α`
  + `{a}`
  + `s.image f`
  + `s.biUnion f`
* + `Filter α`
  + `𝓟 {a}`
  + `Filter.map f F`
  + `Filter.bind F f`
* + `PMF α`
  + the Dirac measure at `a`
  + the image distribution
  + the mixture of the `f a`, weighted by `s`
:::

`Set`, `Filter` and `PMF` are functors without conditions. Only `PMF` is a monad by a global instance; `Set` and `Filter` have monad structures that are not instances, and `Finset` is a monad only when every proposition is decidable. The sections below say why for each.

## Sets
%%%
number := false
tag := "set-monad"
%%%

`Set` is a `Functor`, and `map` is the image:

```lean
example (f : ℕ → ℕ) (s : Set ℕ) : f <$> s = f '' s := rfl
```

The monad structure exists as `Set.monad`, but it is not an instance: sets have no computational content, and a global `Monad Set` would make `do`-notation look like a program. It can be switched on locally:

```lean
section SetMonad
attribute [local instance] Set.monad

def setPairs : Set (ℕ × ℕ) := do
  let x ← ({1, 2, 3} : Set ℕ)
  let y ← ({10, 20} : Set ℕ)
  return (x, y)

example : (3, 10) ∈ setPairs := by
  simp [setPairs]

end SetMonad
```

`bind s f` is `⋃ a ∈ s, f a`, so `setPairs` is the set of pairs `(x, y)` with `x ∈ {1, 2, 3}` and `y ∈ {10, 20}` (the product set `{1, 2, 3} ×ˢ {10, 20}`, typed `\xs`), as the list monad gave a list of the same pairs.

## Finite sets
%%%
number := false
tag := "finset-monad"
%%%

`Finset.image f s` and `Finset.biUnion s f` are `map` and `bind`, but both need `DecidableEq β`: a finite set has no duplicates, so the elements `f a` must be compared. For that reason `Finset` is a `Functor` and a `Monad` only when every proposition is decidable, that is, with the {ref "classical-tactic"}[`classical` tactic] (in a proof) or `open Classical in` (in a definition). In practice one writes `Finset.image` and `Finset.biUnion` directly:

```lean
example : ({1, 2} : Finset ℕ).biUnion (fun n => {n, 10 * n})
    = {1, 2, 10, 20} := by
  decide
```

## Filters
%%%
number := false
tag := "filter-monad"
%%%

For a {ref "filters"}[filter] `F : Filter α`, `Filter.map f F` is the pushforward: `t ∈ Filter.map f F ↔ f ⁻¹' t ∈ F`. `Filter` is a `Functor` with this `map`, and `pure a` is the principal filter `𝓟 {a}`, which contains exactly the sets containing `a`:

```lean
example (f : ℕ → ℕ) (F : Filter ℕ) :
    f <$> F = Filter.map f F := rfl
```

The definition of a limit, `Tendsto f F G ↔ Filter.map f F ≤ G`, is a statement about this `map`.

`Filter.bind` exists too, and `Filter.monad` is a `Monad`, but it is not an instance. `Filter` has a global `<*>`, given by `Filter.seq`. A global `Monad Filter` would bring a second `<*>`, derived from `bind`, and the two differ: a diamond.

`PMF` is the case where the monad is a global instance and the `do`-notation is used in practice. The rest of the chapter is about it.

# Probability mass functions
%%%
tag := "pmf-intro"
%%%

Mathlib's `PMF α` models a *discrete probability distribution* on a
type `α`: it is a function `α → ℝ≥0∞` whose values sum (as a
`tsum`) to `1`.  Unlike full measure theory, working with `PMF` lets
us avoid most measurability hypotheses: the support of a `PMF` is
automatically countable, and there is no σ-algebra on `α` to
keep track of.

The goal of the rest of this chapter is to explain the *monadic*
structure of `PMF`: the four operations `pure`, `bind`, `map`,
`join`, and the laws they satisfy.  This structure is exactly the
one introduced above, now applied to probability distributions.

## Notation and naming conventions
%%%
number := false
tag := "pmf-notation"
%%%

:::table +header
* + Symbol
  + Lean name
  + Reads as
  + Typed as
* + `PMF α`
  + `PMF α`
  + "probability mass function on α"
  + (ASCII)
* + `p a`
  + `DFunLike.coe p a`
  + "the probability of a under p"
  + (ASCII)
* + `p.support`
  + `PMF.support p`
  + "the support of p"
  + (ASCII)
* + `PMF.pure a`
  + `PMF.pure`
  + "the Dirac measure at a"
  + (ASCII)
* + `p.bind f`
  + `PMF.bind`
  + "bind p with f"
  + (ASCII)
* + `p.map f`
  + `PMF.map`
  + "push p along f"
  + (ASCII)
* + `f <$> p`
  + `Functor.map`
  + "f mapped over p"
  + (ASCII)
* + `p >>= f`
  + `Bind.bind`
  + "p bind f"
  + (ASCII)
* + `ℝ≥0∞`
  + `ENNReal`
  + "extended nonneg reals"
  + `\R\ge0\infty`
:::

## The definition
%%%
number := false
tag := "pmf-definition"
%%%

{docstring PMF}

So a `PMF α` is a function `p : α → ℝ≥0∞` together with a proof
`HasSum p 1`. `HasSum f 1` says that the finite sums `∑ a ∈ s, f a`
tend to `1` as `s` grows through the finite sets: it is
`Tendsto (fun s => ∑ a ∈ s, f a) atTop (𝓝 1)`, with the filter `atTop`
on `Finset α` from chapter {ref "filters"}[2.6]. The order of summation
plays no role (unconditional summation). `∑' a, f a` is the value of
the sum (`0` if `f` is not summable).

```lean
example (f : ℕ → ℝ≥0∞) (a : ℝ≥0∞) :
    HasSum f a ↔ Filter.Tendsto
      (fun s : Finset ℕ => ∑ b ∈ s, f b)
      Filter.atTop (𝓝 a) :=
  Iff.rfl
```

In particular:

- `p a : ℝ≥0∞` is the probability mass at `a`;
- `∑' a, p a = 1` (total mass is one);
- `p.support = {a | p a ≠ 0}` is automatically countable.

{docstring PMF.support}

{docstring PMF.support_countable}

The countability of the support is the key reason we can largely
avoid measurability: a discrete distribution only "sees" countably
many values, so an expectation is the sum `∑' a, p a * g a`.

## `pure`: the Dirac distribution
%%%
number := false
tag := "pmf-pure"
%%%

The simplest `PMF` is the *Dirac mass* at a point `a : α`: it
assigns probability `1` to `a` and `0` everywhere else.

{docstring PMF.pure}

The API:

{docstring PMF.pure_apply}

{docstring PMF.support_pure}

```lean
-- `pure 0` on ℕ puts all mass on 0
example : (PMF.pure (0 : ℕ)) 0 = 1 :=
  PMF.pure_apply_self 0

example (n : ℕ) (h : n ≠ 0) : (PMF.pure (0 : ℕ)) n = 0 :=
  PMF.pure_apply_of_ne 0 n h
```

## `bind`: composing distributions
%%%
number := false
tag := "pmf-bind"
%%%

Given `p : PMF α` and a family of distributions
`f : α → PMF β`, the composite distribution `p.bind f : PMF β`
draws `a` according to `p`, then draws `b` according to `f a`.
Its probability mass is

```
(p.bind f) b = ∑' a, p a * (f a) b.
```

{docstring PMF.bind}

{docstring PMF.bind_apply}

The support of the bind is the union of the supports of the
second-stage distributions along the support of the first:

{docstring PMF.support_bind}

The *monad laws* are theorems, proved by computing with sums; no
measurability is needed:

{docstring PMF.pure_bind}

{docstring PMF.bind_pure}

{docstring PMF.bind_bind}

These are the two identity laws and the associativity law introduced
in chapter {ref "type-constructor-classes"}[1.7] (`pure_bind`,
`bind_pure`, `bind_assoc`), here for `PMF`.

## `map`: pushing a distribution along a function
%%%
number := false
tag := "pmf-map"
%%%

If `p : PMF α` and `f : α → β`, the *image distribution*
`p.map f : PMF β` assigns to each `b` the total probability mass
that `p` places on the preimage `f ⁻¹' {b}`.

{docstring PMF.map}

By definition,

```
p.map f = p.bind (pure ∘ f),
```

so `map` is just `bind` composed with `pure`.  This is the generic
derivation of `Functor.map` from the monad operations.

{docstring PMF.map_apply}

{docstring PMF.support_map}

The functor laws, again purely by calculation with `bind`/`pure`:

{docstring PMF.map_id}

{docstring PMF.map_comp}

{docstring PMF.pure_map}

A handy identity relates `bind` and `map`:

{docstring PMF.bind_map}

No measurability hypothesis appears: `PMF.map f p` is defined for
*every* function `f : α → β`. Pushing a measure forward, by contrast,
needs a measurability hypothesis on `f`.

## `join`: flattening distributions of distributions
%%%
number := false
tag := "pmf-join"
%%%

A *distribution of distributions* is a `PMF (PMF α)`: a random
choice of a random variable.  The `join` operation collapses it
into a single `PMF α` by sampling at both stages.

Mathlib has no `PMF.join`; the generic `joinM` (= `bind · id`) works
for every monad. Written out for `PMF`:

```lean
noncomputable def pmfJoin {α : Type} (P : PMF (PMF α)) :
    PMF α :=
  P.bind id

example {α : Type} (p : PMF α) :
    pmfJoin (PMF.pure p) = p :=
  PMF.pure_bind p id
```

Equivalently, unfolding `bind`,

```
(pmfJoin P) a = ∑' q, P q * q a.
```

The general monad identities give us

- `pmfJoin (pure p) = p`  (from `PMF.pure_bind`);
- `pmfJoin (p.map pure) = p`  (from `PMF.bind_pure`);
- `pmfJoin (P.map (fun p ↦ p.map f)) = (pmfJoin P).map f`
  (naturality);
- `pmfJoin (P.map pmfJoin) = pmfJoin (pmfJoin P)`  (associativity),

all derivable from `pure_bind`, `bind_pure`, and `bind_bind`.  No
measurability is used anywhere.

## The `Monad PMF` instance
%%%
number := false
tag := "monad-pmf-instance"
%%%

Everything above is packaged into a `Monad` instance for `PMF`,
so that `do`-notation works out of the box:

```lean
-- Sampling from two dice and returning the sum,
-- in PMF do-notation
noncomputable example (die : PMF (Fin 6)) : PMF ℕ := do
  let x ← die
  let y ← die
  pure (x.val + y.val + 2)
```

The `do`-block is elaborated to

```
die >>= fun x => die >>= fun y => pure (x.val + y.val + 2)
```

and `>>=` on `PMF` is `PMF.bind`:

```lean
example {α β : Type} (p : PMF α) (f : α → PMF β) :
    p >>= f = p.bind f := rfl
```

## Concrete distributions
%%%
number := false
tag := "pmf-concrete"
%%%

Mathlib provides several familiar named distributions as `PMF`s:

- `PMF.uniformOfFintype α : PMF α` — the uniform distribution on a
  finite nonempty type.
- `PMF.uniformOfFinset s hs : PMF α` — the uniform distribution on
  a nonempty finite set.
- `PMF.ofFintype f h : PMF α` — the distribution with weights `f a`
  on a finite type, given `h : ∑ a, f a = 1`.

```lean
-- Fair coin: probability of true is 1/2.
example : PMF.uniformOfFintype Bool true = 1 / 2 := by
  simp [PMF.uniformOfFintype_apply]
```

## Beyond PMFs
%%%
number := false
tag := "pmf-beyond"
%%%

Continuous distributions, such as the uniform distribution on
`[0, 1]` or the normal distribution, are measures `Measure α` on a
σ-algebra `MeasurableSpace α`; they are not part of this course.
`PMF.toMeasure` turns a `PMF` into a measure. `PMF.bernoulli` and
`PMF.binomial` are deprecated; their successors,
`ProbabilityTheory.bernoulliMeasure` and `ProbabilityTheory.binomial`,
are measures.

Discrete probability stays inside `PMF`: no σ-algebra, no
measurability. Composing samplers, pushing them along functions and
computing marginals all happen there.

For further reading: Mathlib's measure-theoretic probability theory
is in the namespace `ProbabilityTheory`, in the files under
`Mathlib/Probability`.
