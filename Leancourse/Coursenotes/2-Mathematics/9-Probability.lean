import VersoManual
import Manual.Meta
import Leancourse.Markup
import Mathlib

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open MyDef

set_option pp.rawOnError true
set_option verso.docstring.allowMissing true

#doc (Manual) "Monads and Probability Mass Functions" =>
%%%
htmlSplit := .never
tag := "probability-pmf"
%%%

`PMF α` is Mathlib's type of discrete probability distributions on `α`. It is a monad in the sense of chapter {ref "type-constructor-classes"}[1.6], and the monad structure is how one builds distributions from others. The chapter first collects the `map` and `bind` operations that have already appeared for sets, finite sets and filters.

# Monads in mathematics
%%%
tag := "monads"
%%%

Chapter {ref "type-constructor-classes"}[1.6] introduced `map`, `pure` and `bind` for `Option` and `List`. The same three operations occur in mathematics, and so far they have appeared under other names:

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

Only `Set` and `Filter` are registered as functors without conditions, and none of the four is a global `Monad`. The sections below say why for each.

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

`bind s f` is `⋃ a ∈ s, f a`, so `setPairs` is the set `{1, 2, 3} ×ˢ {10, 20}`, as the list monad gave a list of the same pairs.

## Finite sets
%%%
number := false
tag := "finset-monad"
%%%

`Finset.image f s` and `Finset.biUnion s f` are `map` and `bind`, but both need `DecidableEq β`: a finite set has no duplicates, so the elements `f a` must be compared. For that reason `Finset` is a `Functor` and a `Monad` only when every proposition is decidable, that is, after the {ref "classical-tactic"}[`classical` tactic] or `open Classical`. In practice one writes `Finset.image` and `Finset.biUnion` directly:

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

`Filter.bind` exists too, and `Filter.monad` is a `Monad`, but it is not an instance. Filters already carry an `Applicative` instance, through `Filter.seq`, and the `seq` that `Filter.monad` derives from `bind` is a different function. One type cannot have both.

`PMF` is the case where the monad is a global instance and the `do`-notation is used in practice. The rest of the chapter is about it.

# Probability mass functions
%%%
tag := "pmf-intro"
%%%

Mathlib's `PMF α` models a *discrete probability distribution* on a
type `α`: it is a function `α → ℝ≥0∞` whose values sum (as a
`tsum`) to `1`.  Unlike full measure theory, working with `PMF` lets
us avoid most measurability hypotheses: the support of a `PMF` is
automatically countable, and there is no {ref "measurable-space"}[sigma-algebra] on `α` to
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
`HasSum p 1`. (xxx: unconditional summation `tsum`/`HasSum` — the crux of `PMF` — is not defined.)  In particular:

- `p a : ℝ≥0∞` is the probability mass at `a`;
- `∑' a, p a = 1` (total mass is one);
- `p.support = {a | p a ≠ 0}` is automatically countable.

{docstring PMF.support}

{docstring PMF.support_countable}

The countability of the support is the key reason we can largely
avoid measurability: a discrete distribution only "sees" countably
many values, so integrals against a `PMF` reduce to infinite sums.

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

The *monad laws* hold by definition (no measurability needed):

{docstring PMF.pure_bind}

{docstring PMF.bind_pure}

{docstring PMF.bind_bind}

These are exactly the two identity laws and the associativity law
introduced earlier in this chapter, specialised from `Option` and
`List` to `PMF`.

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

Notice how no measurability hypothesis appears: `PMF.map f p` makes
sense for *every* function `f : α → β`.  `Measure.map`, by contrast, requires `Measurable f` and produces the
zero measure otherwise.  Measurability only re-enters if we want
to compare `p.map f` with the pushforward measure `p.toMeasure.map f`,
as in `PMF.toMeasure_map_apply` — but nothing on the `PMF` side
requires it.

## `join`: flattening distributions of distributions
%%%
number := false
tag := "pmf-join"
%%%

A *distribution of distributions* is a `PMF (PMF α)`: a random
choice of a random variable.  The `join` operation collapses it
into a single `PMF α` by sampling at both stages.

Mathlib does not define `PMF.join` separately, because every monad
already supplies it as `bind id`.  In Lean:

```lean
-- `join` derived from the monadic structure
noncomputable def PMF.join {α : Type*} (P : PMF (PMF α)) : PMF α :=
  P.bind id
```

Equivalently, unfolding `bind`,

```
(P.join) a = ∑' q, P q * q a.
```

The general monad identities give us

- `join (pure p) = p`  (from `PMF.pure_bind`);
- `join (p.map pure) = p`  (from `PMF.bind_pure`);
- `join (P.map (fun p ↦ p.map f)) = (join P).map f`  (naturality);
- `join (P.map join) = join (join P)`  (associativity of join),

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

Under the hood, this is elaborated to

```
die.bind fun x => die.bind fun y => pure (x.val + y.val + 2).
```

## Concrete distributions
%%%
number := false
tag := "pmf-concrete"
%%%

Mathlib provides several familiar named distributions as `PMF`s:

- `PMF.bernoulli p hp : PMF Bool` — the Bernoulli distribution with
  probability `p` of `true`, requiring `p ≤ 1`.
- `PMF.binomial p hp n : PMF (Fin (n + 1))` — the Binomial
  distribution `B(n, p)`.
- `PMF.uniformOfFinset s hs : PMF α` — the uniform distribution on
  a nonempty finite set.

```lean
-- Fair coin: probability of true is 1/2.
noncomputable example :
    PMF.bernoulli (1 / 2) (by norm_num) true = 1 / 2 := by
  simp [PMF.bernoulli_apply]
```

## Beyond PMFs: measures, expectation, independence
%%%
number := false
tag := "pmf-beyond"
%%%

`PMF` is the right tool for *discrete* distributions, but probability
theory in Mathlib is much larger.  A sketch of where to go next:

- Every `PMF α` induces a probability measure on `α` via
  `PMF.toMeasure`; conversely, {ref "measures"}[`Measure α`] is the general setting
  that handles continuous distributions.
- *Expectation* of a function `f : α → ℝ` against a probability
  measure `μ` is the {ref "integration"}[Bochner integral] `∫ x, f x ∂μ`, found in
  `Mathlib.MeasureTheory.Integral.Bochner`.
- *Independence* of two events / sigma-algebras / random variables
  is `ProbabilityTheory.IndepSets`, `IndepFun`, etc., in
  `Mathlib.Probability.Independence`.
- *Conditional probability* and {ref "conditional-expectation"}[conditional expectation] live in
  `Mathlib.Probability.ConditionalProbability` and the measure-theory
  chapter of these notes.

## When do we still need measurability?
%%%
number := false
tag := "pmf-measurability"
%%%

The `PMF` monad goes a remarkably long way with no mention of
sigma-algebras.  You only need to reach for measurability when:

1. You want to convert a `PMF α` to a Mathlib `Measure α`: this
   uses `PMF.toMeasure`, which *does* require a `MeasurableSpace α`.
2. You want to integrate a function `g : α → ℝ` against a `PMF` and
   reuse the Bochner-integral library.  For discrete sums this is
   usually avoidable; the `PMF`-level API (e.g. `PMF.bind_apply`)
   gives you an explicit `tsum`.
3. You want to compare `PMF.map f` with the measure-theoretic
   pushforward `Measure.map f`.

For most manipulations of discrete distributions — composing
samplers, pushing them along functions, computing marginals —
working directly with `PMF` and its monad laws is cleaner and
measurability-free.
