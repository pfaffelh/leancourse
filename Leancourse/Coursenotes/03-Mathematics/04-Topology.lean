import VersoManual
import Manual.Meta
import Leancourse.Misc.Defs
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

Topology in Mathlib is built on top of the filter framework. Rather than
defining continuity via epsilon-delta or open preimages directly, the primary
definition uses `Filter.Tendsto` applied to neighborhood filters. This section
explains how topological spaces are set up in Mathlib, how continuity works,
and how metric spaces fit in.

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
- Product-related continuity lemmas live in the `Continuous.prod`
  namespace: `Continuous.prodMk`, `Continuous.fst`, `Continuous.snd`.

# TopologicalSpace
%%%
tag := "topological-space"
%%%

A topological space in Mathlib is a typeclass `TopologicalSpace α` that
specifies which sets are open. However, the actual definition in Mathlib
uses the *neighborhood filter* approach: a `TopologicalSpace` is given by
specifying, for each point `x`, its neighborhood filter `nhds x`.

Equivalently, one can define it via `IsOpen`.  Here is the structure
as it appears in Mathlib:

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

- `closure s` -- the smallest closed set containing `s`;
- `interior s` -- the largest open set contained in `s`;
- `frontier s` -- the boundary, defined as `closure s \ interior s`.

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

A function `f : α → β` between topological spaces is *continuous* if it
preserves the neighborhood filter at every point. In Mathlib:

`Continuous f ↔ ∀ x, Filter.Tendsto f (nhds x) (nhds (f x))`

This is equivalent to the classical definition: preimages of open sets are
open.

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
compactness is defined using filters: `s` is compact if every filter that
contains `s` (via the principal filter) and is nontrivial has a cluster point
in `s`.

{docstring IsCompact}

```lean
-- The closed interval [0,1] in ℝ is compact
example : IsCompact (Set.Icc (0 : ℝ) 1) :=
  isCompact_Icc
```

A compact space is one where the whole space is compact:

{docstring CompactSpace}

The image of a compact set under a continuous function is compact:

{docstring IsCompact.image}

# Connected spaces
%%%
tag := "connected-spaces"
%%%

A topological space is *connected* if it cannot be written as the union of
two nonempty disjoint open sets. A set `s` is connected if, viewed as a
subspace, it is connected.

```lean
-- ℝ is connected
#check (inferInstance : ConnectedSpace ℝ)
```

The interval `[a, b]` is connected:

{docstring isPreconnected_Icc}

The continuous image of a connected set is connected:

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
product topology, where a basis of open sets is given by products of open
sets.

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
  + `IsPreconnected s`
* + Metric space
  + `MetricSpace α`
* + Open ball
  + `Metric.ball x r`
* + Distance
  + `dist x y`
:::

The key insight is that all of these interact seamlessly with the filter
framework from the previous section. Limits, continuity, and compactness
are all expressed in terms of filters.
