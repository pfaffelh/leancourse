import VersoManual
import Manual.Meta
import Leancourse.Misc.Defs
import Mathlib

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open MyDef

set_option pp.rawOnError true

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

# TopologicalSpace
%%%
tag := "topological-space"
%%%

A topological space in Mathlib is a typeclass `TopologicalSpace α` that
specifies which sets are open. However, the actual definition in Mathlib
uses the *neighborhood filter* approach: a `TopologicalSpace` is given by
specifying, for each point `x`, its neighborhood filter `nhds x`.

Equivalently, one can define it via `IsOpen`:

```lean
#print TopologicalSpace
-- The key fields are related to which sets are open:
-- IsOpen : Set α → Prop

-- The real numbers have a topological space structure
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

-- Finite intersections and arbitrary unions of open sets are open
#check IsOpen.inter
#check isOpen_iUnion

-- A set is closed iff its complement is open
example {α : Type*} [TopologicalSpace α] (s : Set α) :
    IsClosed s ↔ IsOpen sᶜ :=
  isOpen_compl_iff.symm
```

# The neighborhood filter nhds
%%%
tag := "nhds-filter"
%%%

For a point `x` in a topological space, `nhds x` is the filter of
neighborhoods of `x`. A set `s` is a neighborhood of `x` if there is an open
set `U` with `x ∈ U ⊆ s`.

```lean
#check @nhds
-- nhds : α → Filter α

-- A set is in nhds x iff it contains an open set around x
#check @mem_nhds_iff
-- mem_nhds_iff : s ∈ nhds x ↔ ∃ t ⊆ s, IsOpen t ∧ x ∈ t
```

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

```lean
-- The definition
#check @Continuous
#check @continuous_def
-- continuous_def : Continuous f ↔ ∀ s, IsOpen s → IsOpen (f ⁻¹' s)

-- Equivalence with the filter formulation
#check @continuous_iff_continuousAt
-- Continuous f ↔ ∀ x, ContinuousAt f x
-- where ContinuousAt f x := Tendsto f (nhds x) (nhds (f x))

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

```lean
#check @IsCompact
-- IsCompact : Set α → Prop

-- The closed interval [0,1] in ℝ is compact
example : IsCompact (Set.Icc (0 : ℝ) 1) :=
  isCompact_Icc

-- A compact space is one where the whole space is compact
#check @CompactSpace

-- The image of a compact set under a continuous function is compact
#check @IsCompact.image
```

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

-- The interval [a, b] is connected
#check @isPreconnected_Icc

-- The continuous image of a connected set is connected
#check @IsPreconnected.image
```

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
```lean
-- An open ball
#check @Metric.ball
-- Metric.ball x r = {y | dist x y < r}

-- nhds is generated by open balls
#check @Metric.nhds_basis_ball
```

# Continuity in metric spaces
%%%
tag := "metric-continuity"
%%%

For metric spaces, continuity at a point can be stated in the familiar
epsilon-delta form:

```lean
-- The epsilon-delta characterization
#check @Metric.continuousAt_iff
-- ContinuousAt f x ↔ ∀ ε > 0, ∃ δ > 0, ∀ y, dist y x < δ → dist (f y) (f x) < ε

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

-- A function into a product is continuous iff both components are
#check @Continuous.prodMk
```

# Summary of key Mathlib API for topology
%%%
tag := "topology-api-summary"
%%%

| Concept | Mathlib name |
|---------|-------------|
| Open set | `IsOpen s` |
| Closed set | `IsClosed s` |
| Neighborhood filter | `nhds x` |
| Continuous function | `Continuous f` |
| Continuous at a point | `ContinuousAt f x` |
| Compact set | `IsCompact s` |
| Connected set | `IsPreconnected s` |
| Metric space | `MetricSpace α` |
| Open ball | `Metric.ball x r` |
| Distance | `dist x y` |

The key insight is that all of these interact seamlessly with the filter
framework from the previous section. Limits, continuity, and compactness
are all expressed in terms of filters.
