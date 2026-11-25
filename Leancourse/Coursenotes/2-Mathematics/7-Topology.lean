import VersoManual
import Manual.Meta
import Leancourse.Markup
import Mathlib

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open MyDef

set_option pp.rawOnError true
set_option verso.docstring.allowMissing true

#doc (Manual) "Topology via Filters" =>
%%%
htmlSplit := .never
tag := "topology"
%%%

A topological space in Mathlib is given by its open sets, and a continuous
function is one whose preimages of open sets are open. Most of the theory,
however, is stated with {ref "filters"}[filters]: continuity at a point is
{ref "filter-tendsto"}[`Filter.Tendsto`] on neighbourhood filters, and
compactness is defined with filters directly.

This chapter has no lecture; it is for reading, and sheet `2.7-a` is an extra sheet. No later chapter depends on it. The [slides](slides/2-7-topology/) follow it section by section.

# Notation and naming conventions
%%%
tag := "topology-notation"
%%%

:::table +header
* + Symbol
  + Lean name
  + Reads as
  + Typed as
* + `TopologicalSpace α`
  + `TopologicalSpace α`
  + "topology on α"
  + (ASCII)
* + `IsOpen s`
  + `IsOpen s`
  + "s is open"
  + (ASCII)
* + `IsClosed s`
  + `IsClosed s`
  + "s is closed"
  + (ASCII)
* + `IsClopen s`
  + `IsClopen s`
  + "s is clopen (open and closed)"
  + (ASCII)
* + `nhds x` or `𝓝 x`
  + `nhds x`
  + "neighborhood filter at x"
  + `\nhds`
* + `Continuous f`
  + `Continuous f`
  + "f is continuous"
  + (ASCII)
* + `ContinuousAt f x`
  + `ContinuousAt f x`
  + "f is continuous at x"
  + (ASCII)
* + `IsCompact s`
  + `IsCompact s`
  + "s is compact"
  + (ASCII)
* + `IsConnected s`
  + `IsConnected s`
  + "s is connected"
  + (ASCII)
* + `IsPreconnected s`
  + `IsPreconnected s`
  + "s is preconnected"
  + (ASCII)
* + `dist x y`
  + `dist x y`
  + "distance between x and y"
  + (ASCII)
* + `Metric.ball x r`
  + `Metric.ball x r`
  + "open ball of radius r at x"
  + (ASCII)
* + `Metric.closedBall x r`
  + `Metric.closedBall x r`
  + "closed ball"
  + (ASCII)
* + `f ⁻¹' s`
  + `Set.preimage f s`
  + "preimage of s under f"
  + `\inv'`
* + `f '' s`
  + `Set.image f s`
  + "image of s under f"
  + (ASCII, two `'`)
* + `α × β`
  + `Prod α β`
  + "product of α and β"
  + `\times`
* + `sᶜ`
  + `compl s`
  + "complement of s"
  + `\compl`
:::

Naming hints.

- Predicates over sets are mostly prefixed with `Is`: `IsOpen`,
  `IsClosed`, `IsCompact`, `IsConnected`.
- The filter-flavored counterpart of a property is usually `Tendsto` +
  some filter: `ContinuousAt f x ↔ Tendsto f (𝓝 x) (𝓝 (f x))`.
- `'` and `''` are two different ASCII sequences: `''` is the image
  operator (two apostrophes), while `⁻¹'` is the preimage operator
  (unicode, `\inv'`).
- Continuity lemmas for products: `Continuous.prodMk`,
  `Continuous.fst`, `Continuous.snd`.

# TopologicalSpace
%%%
tag := "topological-space"
%%%

A topological space in Mathlib is a typeclass `TopologicalSpace α` that
specifies which sets are open. Its fields are the predicate `IsOpen` and
the three axioms: the whole space is open, and finite intersections and
arbitrary unions of open sets are open. The neighbourhood filter `nhds x`
is defined from `IsOpen` (see {ref "nhds-filter"}[below]).

{docstring TopologicalSpace}

The real numbers carry the standard topological space structure:

```lean
#check (inferInstance : TopologicalSpace ℝ)
```

# Open and closed sets
%%%
tag := "open-closed-sets"
%%%

- `IsOpen s` : `s` is an open set.
- `IsClosed s` : `sᶜ` is open, i.e., `s` is closed.
- `IsClopen s` : `s` is both open and closed.

```lean
-- The empty set and the whole space are open
example {α : Type*} [TopologicalSpace α] : IsOpen (∅ : Set α) :=
  isOpen_empty

example {α : Type*} [TopologicalSpace α] : IsOpen (Set.univ : Set α) :=
  isOpen_univ

-- A set is closed iff its complement is open
example {α : Type*} [TopologicalSpace α] (s : Set α) :
    IsClosed s ↔ IsOpen sᶜ :=
  isOpen_compl_iff.symm
```

Finite intersections and arbitrary unions of open sets are open:

{docstring IsOpen.inter}

{docstring isOpen_iUnion}

# Closure, interior, and frontier
%%%
tag := "closure-interior"
%%%

For a set `s` in a topological space, three derived sets are
fundamental:

- `closure s` — the smallest closed set containing `s`;
- `interior s` — the largest open set contained in `s`;
- `frontier s` — the boundary, defined as `closure s \ interior s`.

{docstring closure}

{docstring interior}

A point `x` lies in `closure s` if every neighborhood of `x` meets
`s`; equivalently, if `s` is *frequently* close to `x`:

{docstring mem_closure_iff_frequently}

```lean
-- A set is closed iff it equals its closure.
example {α : Type*} [TopologicalSpace α] (s : Set α) :
    IsClosed s ↔ closure s = s :=
  ⟨fun h => h.closure_eq, fun h => h ▸ isClosed_closure⟩

-- The interior of a set is open.
example {α : Type*} [TopologicalSpace α] (s : Set α) :
    IsOpen (interior s) :=
  isOpen_interior
```

# The neighborhood filter nhds
%%%
tag := "nhds-filter"
%%%

For a point `x` in a topological space, `nhds x` is the filter of
neighborhoods of `x`. A set `s` is a neighborhood of `x` if there is an
open set `U` with `x ∈ U ⊆ s`.

{docstring nhds}

{docstring mem_nhds_iff}

The neighborhood filter is the bridge between topology and the filter
framework.

# Continuity via Tendsto
%%%
tag := "continuity-tendsto"
%%%

A function `f : α → β` between topological spaces is *continuous* if
preimages of open sets are open. This is the definition in Mathlib: the
structure `Continuous` has the single field `isOpen_preimage`.
Equivalently, `f` preserves the neighbourhood filter at every point:

`Continuous f ↔ ∀ x, Filter.Tendsto f (nhds x) (nhds (f x))`

The filter form is the one used in most proofs.

{docstring Continuous}

{docstring continuous_def}

Equivalence with the filter formulation:

{docstring continuous_iff_continuousAt}

```lean
-- The identity is continuous
example {α : Type*} [TopologicalSpace α] : Continuous (id : α → α) :=
  continuous_id

-- Composition of continuous functions is continuous
example {α β γ : Type*} [TopologicalSpace α] [TopologicalSpace β]
    [TopologicalSpace γ] (f : α → β) (g : β → γ)
    (hf : Continuous f) (hg : Continuous g) : Continuous (g ∘ f) :=
  hg.comp hf
```

A useful variant is `ContinuousAt f x`, meaning `f` is continuous at
the single point `x`:
```lean
-- ContinuousAt is defined using Tendsto
example {α β : Type*} [TopologicalSpace α] [TopologicalSpace β]
    (f : α → β) (x : α) :
    ContinuousAt f x ↔ Filter.Tendsto f (nhds x) (nhds (f x)) :=
  Iff.rfl
```

# Compact spaces
%%%
tag := "compact-spaces"
%%%

A set `s` is *compact* if every open cover has a finite subcover. In Mathlib,
compactness is defined using filters: `s` is compact if every nontrivial
filter `F` with `F ≤ 𝓟 s` has a cluster point in `s`. A filter is
*nontrivial* (`F.NeBot`) if it is not `⊥`, i.e. `∅ ∉ F`. A point `x` is a
*cluster point* of `F` (`ClusterPt x F`) if `𝓝 x ⊓ F` is nontrivial: every
neighbourhood of `x` meets every set of `F`. For the filter `map u atTop` of
a sequence `u` in a metric space, the cluster points are the limits of
subsequences.

{docstring IsCompact}

```lean
-- The closed interval [0,1] in ℝ is compact
example : IsCompact (Set.Icc (0 : ℝ) 1) :=
  isCompact_Icc
```

A compact space is one where the whole space is compact:

{docstring CompactSpace}

The open-cover definition is a theorem:

{docstring isCompact_iff_finite_subcover}

The image of a compact set under a continuous function is compact:

{docstring IsCompact.image}

# Connected spaces
%%%
tag := "connected-spaces"
%%%

A topological space is *connected* if it cannot be written as the union of
two nonempty disjoint open sets. Mathlib separates this into two
predicates on sets: `IsPreconnected s` says that `s` cannot be split by two
open sets into two nonempty disjoint parts, and `IsConnected s` says in
addition that `s` is nonempty. The empty set is preconnected but not
connected. Most theorems need only the weaker `IsPreconnected`.

```lean
-- ℝ is connected
#check (inferInstance : ConnectedSpace ℝ)
```

The interval `[a, b]` is preconnected, and connected when `a ≤ b`:

{docstring isPreconnected_Icc}

{docstring isConnected_Icc}

The continuous image of a preconnected set is preconnected:

{docstring IsPreconnected.image}

# Metric spaces
%%%
tag := "metric-spaces"
%%%

A `MetricSpace α` provides a distance function `dist : α → α → ℝ` satisfying
the usual axioms. Every metric space is automatically a topological space
(the topology is induced by the metric).

```lean
-- ℝ is a metric space
#check (inferInstance : MetricSpace ℝ)

-- The distance function
#check @dist
-- dist : α → α → ℝ

-- Key properties
example (x y : ℝ) : dist x y ≥ 0 :=
  dist_nonneg

example (x y : ℝ) : dist x y = dist y x :=
  dist_comm x y

-- Triangle inequality
example (x y z : ℝ) : dist x z ≤ dist x y + dist y z :=
  dist_triangle x y z

-- dist x y = 0 iff x = y
example (x y : ℝ) : dist x y = 0 ↔ x = y :=
  dist_eq_zero
```

In a metric space, `nhds x` is generated by open balls:

{docstring Metric.ball}

{docstring Metric.nhds_basis_ball}

# Continuity in metric spaces
%%%
tag := "metric-continuity"
%%%

For metric spaces, continuity at a point can be stated in the familiar
epsilon-delta form:

{docstring Metric.continuousAt_iff}

```lean
-- Example: the function x ↦ 2 * x is continuous on ℝ
example : Continuous (fun x : ℝ ↦ 2 * x) := by
  exact continuous_const.mul continuous_id
```

# Product topology
%%%
tag := "product-topology"
%%%

Given topological spaces `α` and `β`, the product `α × β` carries the
product topology. Its open sets are generated by the products `u ×ˢ v`
of open sets. Here `u ×ˢ v` (typed `\xs`) is the product set: the set
of pairs `(x, y)` with `x ∈ u` and `y ∈ v`.

```lean
-- The product of topological spaces is a topological space
#check (inferInstance : TopologicalSpace (ℝ × ℝ))

-- Projections are continuous
example : Continuous (Prod.fst : ℝ × ℝ → ℝ) :=
  continuous_fst

example : Continuous (Prod.snd : ℝ × ℝ → ℝ) :=
  continuous_snd

```

A function into a product is continuous iff both components are:

{docstring Continuous.prodMk}

# Summary of key Mathlib API for topology
%%%
tag := "topology-api-summary"
%%%

:::table +header
* + Concept
  + Mathlib name
* + Open set
  + `IsOpen s`
* + Closed set
  + `IsClosed s`
* + Neighborhood filter
  + `nhds x`
* + Continuous function
  + `Continuous f`
* + Continuous at a point
  + `ContinuousAt f x`
* + Compact set
  + `IsCompact s`
* + Connected set
  + `IsConnected s` (nonempty), `IsPreconnected s`
* + Metric space
  + `MetricSpace α`
* + Open ball
  + `Metric.ball x r`
* + Distance
  + `dist x y`
:::

Limits, continuity and compactness are all statements about filters
(chapter {ref "filters"}[2.6]).
