import VersoManual
import Manual.Meta
import Leancourse.Misc.Defs
import Mathlib

open Verso.Genre Manual
open MyDef

set_option pp.rawOnError true

#doc (Manual) "Filters in Mathlib" =>
%%%
htmlSplit := .never
tag := "filters"
%%%

Filters are one of the most important and distinctive design choices in
Mathlib. They provide a unified framework for talking about limits,
neighborhoods, convergence, and "eventually" -- replacing the multitude of
epsilon-delta definitions that proliferate in classical analysis textbooks.

# Motivation: why filters?
%%%
tag := "filter-motivation"
%%%

In a traditional analysis course, one encounters many similar-looking
definitions:
- A sequence `a : ℕ → ℝ` converges to `l` if for every `ε > 0` there exists
  `N` such that for all `n ≥ N`, `|a n - l| < ε`.
- A function `f : ℝ → ℝ` has limit `l` at `x₀` if for every `ε > 0` there
  exists `δ > 0` such that for all `x` with `0 < |x - x₀| < δ`,
  `|f x - l| < ε`.
- A function `f : ℝ → ℝ` tends to `+∞` as `x → +∞` if for every `M` there
  exists `N` such that for all `x ≥ N`, `f x ≥ M`.

All of these share the same pattern: "for sufficiently large/close inputs,
the output is in a given set." Filters capture this pattern abstractly.

# Definition of a filter
%%%
tag := "filter-definition"
%%%

A `Filter α` is a collection `F` of sets in `α` satisfying:
1. `Set.univ ∈ F` (the whole space is in the filter).
2. If `s ∈ F` and `s ⊆ t`, then `t ∈ F` (upward closed).
3. If `s ∈ F` and `t ∈ F`, then `s ∩ t ∈ F` (closed under finite intersections).

Intuitively, the sets in a filter are "large" or "eventually true" sets.

```lean
-- The definition in Mathlib
#print Filter

-- A filter is a structure with fields:
-- sets : Set (Set α)
-- univ_sets : Set.univ ∈ sets
-- sets_of_superset : s ∈ sets → s ⊆ t → t ∈ sets
-- inter_sets : s ∈ sets → t ∈ sets → s ∩ t ∈ sets
```

# The principal filter
%%%
tag := "principal-filter"
%%%

The simplest filter is the *principal filter* `Filter.principal s` (or `𝓟 s`),
which consists of all supersets of a given set `s`.

```lean
#check @Filter.principal

-- 𝓟 s contains exactly the supersets of s
example {α : Type*} (s t : Set α) : t ∈ Filter.principal s ↔ s ⊆ t :=
  Filter.mem_principal

-- The principal filter on the whole space is the trivial filter ⊤
example {α : Type*} : Filter.principal (Set.univ : Set α) = ⊤ :=
  Filter.principal_univ
```

# The atTop filter
%%%
tag := "atTop-filter"
%%%

For any linearly ordered type, `Filter.atTop` is the filter of sets that
contain all sufficiently large elements. A set `s` belongs to `Filter.atTop`
if there exists some `a` such that for all `b ≥ a`, `b ∈ s`.

This is the filter we use for limits of sequences.

```lean
#check @Filter.atTop

-- Characterization of membership in atTop
example (s : Set ℕ) : s ∈ Filter.atTop ↔ ∃ a, ∀ b, a ≤ b → b ∈ s :=
  Filter.mem_atTop_sets

-- The set {n : ℕ | n ≥ 100} is in atTop
example : {n : ℕ | n ≥ 100} ∈ (Filter.atTop : Filter ℕ) := by
  rw [Filter.mem_atTop_sets]
  exact ⟨100, fun b hb ↦ hb⟩
```

# Filter.Tendsto: the general notion of limit
%%%
tag := "filter-tendsto"
%%%

The key definition is `Filter.Tendsto f F G`, which means: the preimage of
every set in `G` belongs to `F`. Equivalently, `F.map f ≤ G`.

This single definition unifies all notions of limit:

```lean
#check @Filter.Tendsto
-- Filter.Tendsto (f : α → β) (F : Filter α) (G : Filter β) : Prop
-- Defined as: Filter.map f F ≤ G
-- i.e., ∀ s ∈ G, f ⁻¹' s ∈ F
```

**Limits of sequences**: A sequence `a : ℕ → ℝ` converges to `l` if
`Filter.Tendsto a Filter.atTop (nhds l)`. This says: for every neighborhood
`U` of `l`, the set `{n | a n ∈ U}` is in `atTop`, i.e., `a n ∈ U` for all
sufficiently large `n`.

**Limits of functions at a point**: A function `f : ℝ → ℝ` has limit `l` at
`x₀` if `Filter.Tendsto f (nhds x₀) (nhds l)` (or using `nhdsWithin` for
one-sided limits).

**Limits at infinity**: `Filter.Tendsto f Filter.atTop (nhds l)` means `f(x) → l`
as `x → ∞`.

```lean
-- Sequence convergence in Mathlib
example (a : ℕ → ℝ) (l : ℝ) :
    Filter.Tendsto a Filter.atTop (nhds l) ↔
    ∀ ε > 0, ∃ N, ∀ n ≥ N, |a n - l| < ε := by
  rw [Metric.tendsto_atTop]

-- Composition of limits (if a → l and f is continuous at l, then f ∘ a → f l)
#check @Filter.Tendsto.comp
```

# Filter.Eventually and Filter.Frequently
%%%
tag := "eventually-frequently"
%%%

`Filter.Eventually p F` (notation: `∀ᶠ x in F, p x`) means `{x | p x} ∈ F`.
It captures "the property `p` holds for `F`-almost-all `x`."

`Filter.Frequently p F` (notation: `∃ᶠ x in F, p x`) is the negation of
`Eventually (¬p)`. It means "`p` holds on a `F`-non-negligible set."

```lean
-- Eventually for atTop: "for all sufficiently large n"
example : ∀ᶠ n in Filter.atTop, n ≥ 42 := by
  rw [Filter.eventually_atTop]
  exact ⟨42, fun b hb ↦ hb⟩

-- If p holds eventually and q holds eventually, then p ∧ q holds eventually
example {α : Type*} {F : Filter α} {p q : α → Prop}
    (hp : ∀ᶠ x in F, p x) (hq : ∀ᶠ x in F, q x) :
    ∀ᶠ x in F, p x ∧ q x :=
  hp.and hq

-- Eventually can be combined with Tendsto
#check @Filter.Tendsto.eventually
```

# Filter.map and Filter.comap
%%%
tag := "filter-map-comap"
%%%

- `Filter.map f F` is the *pushforward*: `s ∈ F.map f ↔ f ⁻¹' s ∈ F`.
- `Filter.comap f G` is the *pullback*: `s ∈ F.comap f ↔ ∃ t ∈ G, f ⁻¹' t ⊆ s`.

These form a Galois connection:
`Filter.map f F ≤ G ↔ F ≤ Filter.comap f G`.

```lean
#check @Filter.map_le_iff_le_comap
```

# Ultrafilters
%%%
tag := "ultrafilters"
%%%

An *ultrafilter* is a maximal proper filter: for every set `s`, either `s` or
`sᶜ` belongs to the ultrafilter. Ultrafilters are important in logic (they
correspond to consistent complete theories) and in topology (the Stone-Cech
compactification).

```lean
#check Ultrafilter
-- An ultrafilter on α is a filter F such that for all s, s ∈ F ∨ sᶜ ∈ F

-- Every point gives a principal ultrafilter
#check @Ultrafilter.pure
```

# Why filters are better for formalization
%%%
tag := "filters-advantages"
%%%

Filters may seem abstract at first, but they offer significant advantages
for formal mathematics:

1. **Unification**: One definition of `Tendsto` replaces dozens of epsilon-delta
   definitions.
2. **Composability**: Limits compose naturally via `Filter.Tendsto.comp`.
3. **Algebraic structure**: Filters form a complete lattice, so we can take
   meets and joins of filters.
4. **Avoidance of partial functions**: Instead of "the limit of `f` at `x`"
   (which may not exist), we use `Tendsto f (nhds x) (nhds l)` as a
   proposition.
5. **Smooth interaction with topology**: The neighborhood filter `nhds x` is
   the bridge between filters and topological spaces.
