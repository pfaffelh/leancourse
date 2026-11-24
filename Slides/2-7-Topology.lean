import VersoSlides
import Verso.Doc.Concrete
import Mathlib

open VersoSlides

set_option pp.rawOnError true

/-
Deck for the chapter "Topology via Filters" of part 2 (Mathematics).
It follows the chapter section by section: the class
`TopologicalSpace`, open and closed sets, closure, interior and
frontier, the neighbourhood filter, continuity via `Tendsto`,
compactness, connectedness, metric spaces, continuity in metric
spaces, the product topology, and the API table.
-/

namespace SlidesTopology
open scoped Topology
open Filter

#doc (Slides) "Topology" =>

```css
.reveal section p { font-size: 0.8em; line-height: 1.32; margin: 0.42em 0; }
.reveal section p.key, .reveal section .key p { color: #1b91ff; }
.reveal section table { font-size: 0.62em; margin: 0.2em auto 0.4em; }
.reveal section table th,
.reveal section table td { padding: 0.18em 0.9em; }
.reveal section li { font-size: 0.8em; }
.reveal section .small table, .reveal section table.small { font-size: 0.5em; }
.reveal section .small table code, .reveal section table.small code { font-size: 0.95em; }
.reveal section .small td, .reveal section table.small td { padding: 0.1em 0.6em; }
```

# Topology

Mathematics — chapter 7

:::class "key"
A topology says which sets are open. From it come the neighbourhood filters `𝓝 x`, and continuity and compactness are statements about these filters.
:::

# The class TopologicalSpace

```
class TopologicalSpace (X : Type u) where
  IsOpen : Set X → Prop
  isOpen_univ : IsOpen univ
  isOpen_inter : ∀ s t, IsOpen s → IsOpen t →
    IsOpen (s ∩ t)
  isOpen_sUnion : ∀ s, (∀ t ∈ s, IsOpen t) →
    IsOpen (⋃₀ s)
```

```lean -panel -stretch
#check (inferInstance : TopologicalSpace ℝ)
```

:::class "key"
A topology is a predicate `IsOpen` on `Set X` with three axioms. It is a class: `ℝ` gets its topology by instance search.
:::

# Open and closed sets

:::table +colHeaders +rowSeps
*
  * predicate
  * meaning
*
  * `IsOpen s`
  * `s` is open
*
  * `IsClosed s`
  * `sᶜ` is open
*
  * `IsClopen s`
  * open and closed
:::

```lean -panel -stretch
variable {X Y : Type*}
  [TopologicalSpace X] [TopologicalSpace Y]
example : IsOpen (∅ : Set X) := isOpen_empty
example : IsOpen (Set.univ : Set X) := isOpen_univ
example (s : Set X) : IsClosed s ↔ IsOpen sᶜ :=
  isOpen_compl_iff.symm
```

`∅` is open as the union of the empty family.

# Unions and intersections

```lean -panel -stretch
example (s t : Set X) (hs : IsOpen s) (ht : IsOpen t) :
    IsOpen (s ∩ t) :=
  hs.inter ht
example {ι : Type*} (U : ι → Set X)
    (h : ∀ i, IsOpen (U i)) : IsOpen (⋃ i, U i) :=
  isOpen_iUnion h
example (a b : ℝ) : IsOpen (Set.Ioo a b) := isOpen_Ioo
example (a b : ℝ) : IsClosed (Set.Icc a b) := isClosed_Icc
```

:::class "key"
Finite intersections and arbitrary unions of open sets are open.
:::

# Closure, interior, frontier

:::table +colHeaders +rowSeps
*
  * set
  * description
*
  * `closure s`
  * the smallest closed set containing `s`
*
  * `interior s`
  * the largest open set contained in `s`
*
  * `frontier s`
  * `closure s \ interior s`
:::

```lean -panel -stretch
example (s : Set X) : IsClosed s ↔ closure s = s :=
  ⟨fun h => h.closure_eq, fun h => h ▸ isClosed_closure⟩
example (s : Set X) : IsOpen (interior s) :=
  isOpen_interior
```

# Intervals in ℝ

```lean -panel -stretch
example (a b : ℝ) (h : a ≠ b) :
    closure (Set.Ioo a b) = Set.Icc a b :=
  closure_Ioo h
example (a b : ℝ) :
    interior (Set.Icc a b) = Set.Ioo a b :=
  interior_Icc
example (a b : ℝ) (h : a ≤ b) :
    frontier (Set.Icc a b) = {a, b} :=
  frontier_Icc h
```

:::class "key"
The hypotheses matter: for `a = b` the interval `Ioo a a` is empty, and so is its closure.
:::

# The neighbourhood filter

`s` is a neighbourhood of `x` if an open set `t` lies between: `x ∈ t ⊆ s`. The neighbourhoods of `x` form a filter, `𝓝 x` (`nhds x`).

```lean -panel -stretch
example (x : X) (s : Set X) :
    s ∈ 𝓝 x ↔ ∃ t ⊆ s, IsOpen t ∧ x ∈ t :=
  mem_nhds_iff
example (s : Set X) :
    IsOpen s ↔ ∀ x ∈ s, s ∈ 𝓝 x :=
  isOpen_iff_mem_nhds
```

:::class "key"
`𝓝 x` is the generalized subset "points close to `x`".
:::

# Closure through filters

```lean -panel -stretch
example (x : X) (s : Set X) :
    x ∈ closure s ↔ ∃ᶠ y in 𝓝 x, y ∈ s :=
  mem_closure_iff_frequently
```

`x ∈ closure s` says: `s` is not negligible near `x`, so every neighbourhood of `x` meets `s`.

:::class "key"
Topological notions are statements about `𝓝 x`, written with `∀ᶠ`, `∃ᶠ` and `Tendsto` from chapter 6.
:::

# Continuity at a point

```lean -panel -stretch
example (f : X → Y) (x : X) :
    ContinuousAt f x ↔ Tendsto f (𝓝 x) (𝓝 (f x)) :=
  Iff.rfl
```

`f x'` is close to `f x` whenever `x'` is close enough to `x`: the map `f` sends the filter `𝓝 x` into `𝓝 (f x)`.

:::class "key"
`ContinuousAt` is defined by `Tendsto`; `Iff.rfl` proves the unfolding.
:::

# Continuous functions

```
structure Continuous (f : X → Y) : Prop where
  isOpen_preimage : ∀ s, IsOpen s → IsOpen (f ⁻¹' s)
```

```lean -panel -stretch
example (f : X → Y) : Continuous f ↔
    ∀ s, IsOpen s → IsOpen (f ⁻¹' s) :=
  continuous_def
example (f : X → Y) :
    Continuous f ↔ ∀ x, ContinuousAt f x :=
  continuous_iff_continuousAt
```

:::class "key"
`Continuous` is defined by preimages of open sets. Continuity at every point is an equivalent form, and a theorem.
:::

# Building continuous functions

```lean -panel -stretch
example : Continuous (id : X → X) := continuous_id
example {Z : Type*} [TopologicalSpace Z] (f : X → Y)
    (g : Y → Z) (hf : Continuous f)
    (hg : Continuous g) : Continuous (g ∘ f) :=
  hg.comp hf
example : Continuous (fun x : ℝ ↦ 2 * x) :=
  continuous_const.mul continuous_id
example : Continuous (fun x : ℝ ↦ Real.exp (x ^ 2)) := by
  fun_prop
```

`fun_prop` takes the function apart and applies the lemmas for constants, sums, products and compositions.

# Compactness

Classically: every open cover of `s` has a finite subcover. In Mathlib:

```
def IsCompact (s : Set X) :=
  ∀ ⦃f⦄ [NeBot f], f ≤ 𝓟 s → ∃ x ∈ s, ClusterPt x f
```

:::table +colHeaders +rowSeps
*
  * in the definition
  * reads
*
  * `NeBot f`
  * `f ≠ ⊥`: `f` does not contain `∅`
*
  * `f ≤ 𝓟 s`
  * `s ∈ f`: the generalized subset `f` lies in `s`
*
  * `ClusterPt x f`
  * every set in `f` meets every neighbourhood of `x`
:::

:::class "key"
`s` is compact if every nontrivial filter on `s` clusters at some point of `s`.
:::

# Nontrivial filters and cluster points

```lean -panel -stretch
example (f : Filter X) : NeBot f ↔ f ≠ ⊥ :=
  neBot_iff
example (x : X) (f : Filter X) : ClusterPt x f ↔
    ∀ U ∈ 𝓝 x, ∀ V ∈ f, (U ∩ V).Nonempty := by
  rw [clusterPt_iff_nonempty]
example (x : X) (s : Set X) :
    ClusterPt x (𝓟 s) ↔ x ∈ closure s :=
  mem_closure_iff_clusterPt.symm
```

For a sequence `u`, a cluster point of `map u atTop` is the limit of a subsequence (in a metric space).

# Compactness in practice

```lean -panel -stretch
example : IsCompact (Set.Icc (0 : ℝ) 1) := isCompact_Icc
example (f : X → Y) (s : Set X) (hs : IsCompact s)
    (hf : Continuous f) : IsCompact (f '' s) :=
  hs.image hf
```

`CompactSpace X` says that `Set.univ` is compact. A continuous `f : X → ℝ` attains its minimum on a nonempty compact set: `IsCompact.exists_isMinOn`.

:::class "key"
The open-cover definition is a theorem, `isCompact_iff_finite_subcover`.
:::

# Connectedness

```
def IsPreconnected (s : Set α) : Prop :=
  ∀ u v : Set α, IsOpen u → IsOpen v →
    s ⊆ u ∪ v → (s ∩ u).Nonempty →
    (s ∩ v).Nonempty → (s ∩ (u ∩ v)).Nonempty

def IsConnected (s : Set α) : Prop :=
  s.Nonempty ∧ IsPreconnected s
```

:::class "key"
Two open sets that cover `s` and both meet `s` must meet inside `s`. Connected means preconnected and nonempty; `∅` is preconnected, not connected.
:::

# Connected sets in ℝ

```lean -panel -stretch
#check (inferInstance : ConnectedSpace ℝ)
example (a b : ℝ) : IsPreconnected (Set.Icc a b) :=
  isPreconnected_Icc
example (a b : ℝ) (h : a ≤ b) :
    IsConnected (Set.Icc a b) :=
  isConnected_Icc h
example (f : X → Y) (s : Set X) (hs : IsPreconnected s)
    (hf : Continuous f) : IsPreconnected (f '' s) :=
  hs.image f hf.continuousOn
```

`IsPreconnected` needs no hypothesis on `a, b`. With `IsConnected` the theorem needs `a ≤ b`.

# Metric spaces

`MetricSpace X` provides `dist : X → X → ℝ` with the usual axioms. A metric space is a topological space by instance.

```lean -panel -stretch
example (x y : ℝ) : 0 ≤ dist x y := dist_nonneg
example (x y : ℝ) : dist x y = dist y x := dist_comm x y
example (x y z : ℝ) :
    dist x z ≤ dist x y + dist y z :=
  dist_triangle x y z
example (x y : ℝ) : dist x y = 0 ↔ x = y := dist_eq_zero
example (x y : ℝ) : dist x y = |x - y| := Real.dist_eq x y
```

# Balls

```lean -panel -stretch
example (x y : ℝ) (r : ℝ) :
    y ∈ Metric.ball x r ↔ dist y x < r :=
  Metric.mem_ball
example (x : ℝ) (s : Set ℝ) :
    s ∈ 𝓝 x ↔ ∃ ε > 0, Metric.ball x ε ⊆ s :=
  Metric.mem_nhds_iff
#check @Metric.nhds_basis_ball
```

:::class "key"
In a metric space, `𝓝 x` is generated by the balls around `x`: a set is a neighbourhood if it contains a ball.
:::

# ε and δ from Tendsto

```lean -panel -stretch
example (f : ℝ → ℝ) : Continuous f ↔
    ∀ b, ∀ ε > 0, ∃ δ > 0, ∀ a,
      dist a b < δ → dist (f a) (f b) < ε :=
  Metric.continuous_iff
```

Proof in Mathlib: `continuous_iff_continuousAt`, then unfold `Tendsto f (𝓝 b) (𝓝 (f b))` with the ball basis on both sides.

:::class "key"
The ε-δ definition is a theorem about metric spaces, not the definition of continuity.
:::

# An ε-δ proof

```lean -panel -stretch
example : Continuous (fun x : ℝ ↦ 2 * x) := by
  rw [Metric.continuous_iff]
  intro b ε hε
  refine ⟨ε / 2, half_pos hε, fun a ha => ?_⟩
  rw [Real.dist_eq] at *
  calc |2 * a - 2 * b| = 2 * |a - b| := by
        rw [← mul_sub, abs_mul, abs_two]
    _ < ε := by linarith
```

The same statement is `continuous_const.mul continuous_id`, or `fun_prop`.

# Product topology

The open sets of `X × Y` are generated by the products `u ×ˢ v` of open sets.

```lean -panel -stretch
#check (inferInstance : TopologicalSpace (ℝ × ℝ))
example : Continuous (Prod.fst : ℝ × ℝ → ℝ) :=
  continuous_fst
example : Continuous (Prod.snd : ℝ × ℝ → ℝ) :=
  continuous_snd
example (f : X → ℝ) (g : X → ℝ) (hf : Continuous f)
    (hg : Continuous g) :
    Continuous (fun x ↦ (f x, g x)) :=
  hf.prodMk hg
```

:::class "key"
A map into a product is continuous if both components are.
:::

# The API

::::class "small"
:::table +colHeaders +rowSeps
*
  * concept
  * Mathlib
  * defined via
*
  * open, closed set
  * `IsOpen s`, `IsClosed s`
  * the class, `IsOpen sᶜ`
*
  * neighbourhood filter
  * `𝓝 x`
  * open sets containing `x`
*
  * continuous at a point
  * `ContinuousAt f x`
  * `Tendsto f (𝓝 x) (𝓝 (f x))`
*
  * continuous
  * `Continuous f`
  * preimages of open sets
*
  * compact set
  * `IsCompact s`
  * cluster points of filters
*
  * (pre)connected set
  * `IsConnected s`, `IsPreconnected s`
  * open covers by two sets
*
  * distance, ball
  * `dist x y`, `Metric.ball x r`
  * `MetricSpace α`
:::
::::

# Summary

- A topology is the class `TopologicalSpace`: a predicate `IsOpen` with three axioms.
- `𝓝 x` turns the topology into a filter; closure, continuity at a point and compactness are statements about `𝓝 x`.
- `Continuous` is defined by preimages; `continuous_iff_continuousAt` connects it with `Tendsto`.
- Compactness is defined by cluster points of filters; finite subcovers are a theorem.
- In a metric space, `𝓝 x` is generated by balls, and ε-δ is the theorem `Metric.continuous_iff`.
