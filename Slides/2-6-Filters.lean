import VersoSlides
import Verso.Doc.Concrete
import Mathlib

open VersoSlides

set_option pp.rawOnError true

/-
Deck for the chapter "Filters in Mathlib" of part 2 (Mathematics). It
follows the chapter section by section: motivation, filters as
generalized subsets, the definition, the order, principal filter,
`atTop`, `cofinite`, the neighbourhood filter `𝓝 x`, `map` and `comap`, `Tendsto`, `Eventually` and
`Frequently`, the worked example `1 / (n + 1) → 0`, ultrafilters, why
filters suit formalization. The notation table, which opens the
chapter, comes here at the end as a reference.
-/

namespace SlidesFilters
open Filter Topology

#doc (Slides) "Filters in Mathlib" =>

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

# Filters

Mathematics — chapter 6

:::class "key"
A filter is a *generalized subset*. One definition of limit covers sequences, functions and limits at infinity.
:::

:::notes
The one idea of the lecture. Come back to it.
:::

# The problem

Three $`\varepsilon`-$`\delta` definitions:

- $`a_n \to l`: $`\forall \varepsilon > 0, \exists N, \forall n \ge N, |a_n - l| < \varepsilon`

- $`f(x) \to l` as $`x \to x_0`: $`\forall \varepsilon > 0, \exists \delta > 0, \forall x, 0 < |x - x_0| < \delta \Rightarrow |f(x) - l| < \varepsilon`

- $`f(x) \to \infty` as $`x \to \infty`: $`\forall M, \exists N, \forall x \ge N, f(x) \ge M`

:::class "key"
One shape: *for good enough inputs, the output lies in a given set.*
:::

:::notes
Do not read the quantifiers out loud — the students know them.
The point is only that the three look alike.
:::

# The idea

A filter on $`\alpha` is a *generalized subset* of $`\alpha`. Every subset gives a filter. Other filters stand for ideas no single subset describes: an infinitesimal neighbourhood of a point, a neighbourhood of $`\infty`.

Newton wanted $`dx` to be a number infinitesimally close to $`0`.
A filter is how we get that back.

:::class "key"
A generalized subset $`F` of $`\alpha` is pinned down by the *actual* sets that contain it.
:::

:::notes
Stress that we never say what F *is* — only which sets contain it.
That move is the whole trick.
:::

# The three axioms

The sets that may contain $`F`:

:::table +rowHeaders +rowSeps
*
  * 1
  * $`S \supseteq F` and $`S \subseteq T`  $`\Rightarrow`  $`T \supseteq F`
*
  * 2
  * $`S \supseteq F` and $`T \supseteq F`  $`\Rightarrow`  $`S \cap T \supseteq F`
*
  * 3
  * $`\alpha \supseteq F`
:::

:::class "key"
A filter is a collection of subsets of $`\alpha` with these three properties.
:::

# In Lean

```lean -panel -stretch
structure MyFilter (α : Type) where
  sets : Set (Set α)
  univ_sets : Set.univ ∈ sets
  sets_of_superset {x y} :
    x ∈ sets → x ⊆ y → y ∈ sets
  inter_sets {x y} :
    x ∈ sets → y ∈ sets → x ∩ y ∈ sets
```

Mathlib's `Filter α` has the same three fields. For `F : Filter α` and `S : Set α`, `S ∈ F` means `S ∈ F.sets`.

:::class "key"
`S ∈ F` morally means `F ⊆ S`. That expression does not type-check: `F` is not a set.
:::

# The axioms in Mathlib

```
Filter.univ_mem        : univ ∈ f
Filter.mem_of_superset : x ∈ f → x ⊆ y → y ∈ f
Filter.inter_mem       : s ∈ f → t ∈ f → s ∩ t ∈ f
```

Some authors add a fourth axiom: $`\emptyset \notin F`. Mathlib does not. The filter containing every set, `⊥`, is a filter, as a ring is an ideal of itself.

:::class "key"
With `⊥` allowed, the meet `F ⊓ G` (sets `a ∩ b`, `a ∈ F`, `b ∈ G`) is always a filter: `𝓟 s ⊓ 𝓟 sᶜ = ⊥`. Without it, every `⊓` would need a proof of properness.
:::

# The order on filters

`F ≤ G` is defined as `G.sets ⊆ F.sets`. If `F` lies inside `G` as generalized subsets, every set containing `G` contains `F`.

```lean -panel -stretch
example {α : Type*} (F G : Filter α) :
    F ≤ G ↔ ∀ s ∈ G, s ∈ F := Filter.le_def
example {α : Type*} (s : Set α) :
    s ∈ (⊥ : Filter α) := Filter.mem_bot
example {α : Type*} (s : Set α) :
    s ∈ (⊤ : Filter α) ↔ s = Set.univ := Filter.mem_top
```

:::class "key"
The smaller the filter, the more sets it has. Read `F ≤ G` as "F is finer than G".
:::

# The principal filter

`𝓟 s` has exactly the supersets of `s` as its sets: the generalized subset given by the ordinary subset `s`.

```lean -panel -stretch
example {α : Type*} (s t : Set α) :
    t ∈ 𝓟 s ↔ s ⊆ t := mem_principal
example {α : Type*} (s : Set α) : s ∈ 𝓟 s :=
  mem_principal_self s
example {α : Type*} : 𝓟 (Set.univ : Set α) = ⊤ :=
  principal_univ
example {α : Type*} (s t : Set α) :
    𝓟 s ≤ 𝓟 t ↔ s ⊆ t := principal_mono
```

:::class "key"
On principal filters, `≤` is `⊆`.
:::

# The filter `atTop`

On a preorder, `atTop` contains the sets that contain all sufficiently large elements: a neighbourhood of $`\infty`, although there is no largest element.

```lean -panel -stretch
example (s : Set ℕ) :
    s ∈ (atTop : Filter ℕ) ↔ ∃ a, ∀ b, a ≤ b → b ∈ s :=
  mem_atTop_sets

example : {n : ℕ | n ≥ 100} ∈ (atTop : Filter ℕ) := by
  rw [mem_atTop_sets]
  exact ⟨100, fun b hb ↦ hb⟩
```

:::class "key"
A set is in `atTop` if it contains a tail `[a, ∞)`.
:::

# The filter `cofinite`

`cofinite` contains the sets with finite complement: "almost every element".

```lean -panel -stretch
example (α : Type*) (s : Set α) :
    s ∈ (cofinite : Filter α) ↔ sᶜ.Finite := Iff.rfl
example : (cofinite : Filter ℕ) = atTop :=
  Nat.cofinite_eq_atTop
example : (cofinite : Filter ℤ) = atBot ⊔ atTop :=
  Int.cofinite_eq
```

:::class "key"
On `ℕ`, `cofinite` and `atTop` coincide. On `ℤ` they differ: a cofinite set contains both tails. `atBot`: sets containing a tail `(-∞, a]`.
:::

# The neighbourhood filter `𝓝 x`

`s ∈ 𝓝 x`: `s` contains an open set around `x`. On `ℝ`: an interval $`(x - \varepsilon, x + \varepsilon)`.

```lean -panel -stretch
example (x : ℝ) (s : Set ℝ) :
    s ∈ 𝓝 x ↔ ∃ ε > 0, Set.Ioo (x - ε) (x + ε) ⊆ s := by
  simp [Metric.mem_nhds_iff, Real.ball_eq_Ioo]
```

:::class "key"
`𝓝 x` is the generalized subset "points infinitesimally close to `x`". General spaces: chapter 2.7 (reading).
:::

# `Filter.map`: the pushforward

For `m : α → β` and `F : Filter α`, a set `s : Set β` is in `map m F` if its preimage is in `F`. This is the counterpart of the image of a subset.

```lean -panel -stretch
example {α β : Type*} (m : α → β) (F : Filter α)
    (s : Set β) : s ∈ map m F ↔ m ⁻¹' s ∈ F := Iff.rfl
example {α β : Type*} (m : α → β) (s : Set α) :
    map m (𝓟 s) = 𝓟 (m '' s) := map_principal
```

:::class "key"
`map m (𝓟 s) = 𝓟 (m '' s)`: the pushforward of a principal filter is the principal filter of the image.
:::

# `Filter.comap`: the pullback

`comap m G`: the filter generated by the preimages `m ⁻¹' t`, `t ∈ G`, the counterpart of the preimage.

```lean -panel -stretch
example {α β : Type*} (m : α → β) (G : Filter β)
    (s : Set α) :
    s ∈ comap m G ↔ ∃ t ∈ G, m ⁻¹' t ⊆ s := mem_comap
example {α β : Type*} (m : α → β) (F : Filter α)
    (G : Filter β) :
    map m F ≤ G ↔ F ≤ comap m G := map_le_iff_le_comap
```

:::class "key"
`map m F ≤ G ↔ F ≤ comap m G`, as `m '' s ⊆ t ↔ s ⊆ m ⁻¹' t` (chapter 2.2). A pair of maps with this property is a *Galois connection* (`GaloisConnection`, lemma `Filter.gc_map_comap`).
:::

# `Filter.Tendsto`

```lean -panel -stretch
example {α β : Type*} (f : α → β) (F : Filter α)
    (G : Filter β) : Tendsto f F G ↔ map f F ≤ G :=
  Iff.rfl
example {α β : Type*} (f : α → β) (F : Filter α)
    (G : Filter β) :
    Tendsto f F G ↔ ∀ s ∈ G, f ⁻¹' s ∈ F := tendsto_def
```

For every `s ∈ G`, the preimage `f ⁻¹' s` is in `F`.

:::class "key"
`Tendsto f F G`: `f` maps the generalized subset `F` into the generalized subset `G`.
:::

# One definition instead of three

:::table +colHeaders +rowSeps
*
  * classical statement
  * filter version
*
  * $`a_n \to l` as $`n \to \infty`
  * `Tendsto a atTop (𝓝 l)`
*
  * $`f(x) \to l` as $`x \to x_0`
  * `Tendsto f (𝓝[≠] x₀) (𝓝 l)`
*
  * $`f(x) \to l` as $`x \to \infty`
  * `Tendsto f atTop (𝓝 l)`
*
  * $`f(x) \to \infty` as $`x \to \infty`
  * `Tendsto f atTop atTop`
:::

`𝓝[≠] x₀ = 𝓝 x₀ ⊓ 𝓟 {x₀}ᶜ`: near `x₀`, without `x₀`.

:::class "key"
Change the two filters, keep the definition.
:::

:::notes
The same definition gives sequence limits, function limits and limits
at infinity.
:::

# Check: sequences

`Metric.tendsto_atTop`: `Tendsto u atTop (𝓝 a) ↔ ∀ ε > 0, ∃ N, ∀ n ≥ N, dist (u n) a < ε`. On `ℝ`, `dist x y = |x - y|` (`Real.dist_eq`).

```lean -panel -stretch
example (a : ℕ → ℝ) (l : ℝ) :
    Tendsto a atTop (𝓝 l) ↔
    ∀ ε > 0, ∃ N, ∀ n ≥ N, |a n - l| < ε := by
  rw [Metric.tendsto_atTop]
  simp [Real.dist_eq]
```

:::class "key"
For sequences in `ℝ`, `Tendsto` is the $`\varepsilon`-$`N` definition.
:::

# Check: limits of functions

```lean -panel -stretch
example (x₀ : ℝ) : 𝓝[≠] x₀ = 𝓝 x₀ ⊓ 𝓟 {x₀}ᶜ := rfl
example (f : ℝ → ℝ) (x₀ l : ℝ) :
    Tendsto f (𝓝[≠] x₀) (𝓝 l) ↔ ∀ ε > 0, ∃ δ > 0,
      ∀ x, x ≠ x₀ → |x - x₀| < δ → |f x - l| < ε := by
  rw [Metric.tendsto_nhdsWithin_nhds]
  simp [Real.dist_eq]
```

:::class "key"
With `𝓝 x₀` in place of `𝓝[≠] x₀`, the value at `x₀` would count and force `l = f x₀`: that is continuity at `x₀`.
:::

# Composition

```
Tendsto.comp :
  Tendsto g G H → Tendsto f F G → Tendsto (g ∘ f) F H
Continuous.tendsto :
  Continuous f → ∀ x, Tendsto f (𝓝 x) (𝓝 (f x))
```

```lean -panel -stretch
example {a : ℕ → ℝ} {l : ℝ} (h : Tendsto a atTop (𝓝 l)) :
    Tendsto (fun n => Real.exp (a n)) atTop
      (𝓝 (Real.exp l)) :=
  (Real.continuous_exp.tendsto l).comp h
```

:::class "key"
Continuity at `x` *is* `Tendsto f (𝓝 x) (𝓝 (f x))` (definition `ContinuousAt`, chapter 2.7). If `a → l` and `f` is continuous at `l`, then `f ∘ a → f l`: one lemma, `Tendsto.comp`.
:::

# `Filter.Eventually`

`∀ᶠ x in F, p x` is defined as `{x | p x} ∈ F`: `p` holds for generalized-almost-all `x`.

```lean -panel -stretch
example {α : Type*} (p : α → Prop) (F : Filter α) :
    (∀ᶠ x in F, p x) ↔ {x | p x} ∈ F := Iff.rfl
example {p : ℕ → Prop} :
    (∀ᶠ n in atTop, p n) ↔ ∃ N, ∀ n ≥ N, p n :=
  eventually_atTop
```

- `atTop`: for all sufficiently large `n`,
- `𝓝 x₀`: on a neighbourhood of `x₀`,
- `cofinite`: off a finite set.

# `Filter.Frequently`

`∃ᶠ x in F, p x` is `¬ ∀ᶠ x in F, ¬ p x`: `p` holds on a set that is not negligible for `F`.

```lean -panel -stretch
example {α : Type*} (p : α → Prop) (F : Filter α) :
    (∃ᶠ x in F, p x) ↔ ¬ ∀ᶠ x in F, ¬ p x := Iff.rfl
example {p : ℕ → Prop} :
    (∃ᶠ n in atTop, p n) ↔ ∀ N, ∃ n ≥ N, p n :=
  frequently_atTop
```

:::class "key"
Along `atTop` on `ℕ`: `∀ᶠ` is "from some point on", `∃ᶠ` is "infinitely often".
:::

# `filter_upwards`

```lean -panel -stretch
example {α : Type*} {F : Filter α} {p q : α → Prop}
    (hp : ∀ᶠ x in F, p x) (hq : ∀ᶠ x in F, q x) :
    ∀ᶠ x in F, p x ∧ q x :=
  hp.and hq

example {α : Type*} {F : Filter α} {p q : α → Prop}
    (hp : ∀ᶠ x in F, p x) (hq : ∀ᶠ x in F, q x) :
    ∀ᶠ x in F, p x ∧ q x := by
  filter_upwards [hp, hq] with x hp hq
  exact ⟨hp, hq⟩
```

:::class "key"
`filter_upwards [h₁, h₂] with x h₁ h₂` intersects the hypotheses and leaves the pointwise goal.
:::

# A worked example: 1/(n+1) → 0

```lean -panel -stretch
example : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1))
    atTop (𝓝 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  -- Archimedes: some N > 1/ε
  obtain ⟨N, hN⟩ := exists_nat_gt (1 / ε)
  refine ⟨N, fun n hn => ?_⟩
  have hn' : (N : ℝ) ≤ n := by exact_mod_cast hn
  rw [div_lt_iff₀ hε] at hN
  rw [Real.dist_eq, sub_zero, abs_of_pos (by positivity),
    div_lt_iff₀ (by positivity)]
  calc (1 : ℝ) < N * ε := hN
    _ ≤ n * ε := mul_le_mul_of_nonneg_right hn' hε.le
    _ < ε * (n + 1) := by linarith
```

:::class "key"
The statement takes one line. The work is the same inequality as in the $`\varepsilon`-$`N` proof.
:::

# Ultrafilters

A filter `F` is *proper* if `F ≠ ⊥`, that is $`\emptyset \notin F`. An *ultrafilter* is a maximal proper filter: for every set `s`, exactly one of `s` and `sᶜ` belongs to it.

```lean -panel -stretch
example {α : Type*} (U : Ultrafilter α) (s : Set α) :
    s ∈ U ∨ sᶜ ∈ U := Ultrafilter.mem_or_compl_mem U s
example (s : Set ℕ) :
    s ∈ (pure 3 : Ultrafilter ℕ) ↔ 3 ∈ s :=
  Ultrafilter.mem_pure
```

`pure 3`: the principal ultrafilter, the sets containing `3`. Non-principal ultrafilters exist only by choice (`Ultrafilter.of`, Zorn).

Ultrafilters appear in logic (complete consistent theories) and topology (compactifications, nonstandard analysis).

# Why filters suit formalization

- *One definition.* `Tendsto` replaces dozens of $`\varepsilon`-$`\delta` variants.

- *Composition.* Limits compose with `Tendsto.comp`.

- *Order.* Filters form a complete lattice: meets and joins of families exist.

- *No partial functions.* Instead of "the limit of `f` at `x`", which may not exist, the proposition `Tendsto f (𝓝 x) (𝓝 l)`.

- *Topology.* The neighbourhood filter `𝓝 x` connects filters with topological spaces.

# Notation

::::class "small"
:::table +colHeaders +rowSeps
*
  * symbol
  * Lean name
  * reads as
  * typed as
*
  * `s ∈ F`
  * `s ∈ F.sets`
  * s is F-large; morally `F ⊆ s`
  * `\in`
*
  * `F ≤ G`
  * `LE.le F G`
  * F is finer than G
  * `\le`
*
  * `𝓟 s`
  * `Filter.principal s`
  * the principal filter of s
  * `\McP`
*
  * `𝓝 x`
  * `nhds x`
  * the neighbourhood filter at x
  * `\nhds`
*
  * `f ⁻¹' s`
  * `Set.preimage f s`
  * the preimage of s under f
  * `\inv'`
*
  * `∀ᶠ x in F, p x`
  * `Filter.Eventually p F`
  * eventually p, along F
  * `\all\^f`
*
  * `∃ᶠ x in F, p x`
  * `Filter.Frequently p F`
  * frequently p, along F
  * `\ex\^f`
:::
::::

# Summary

- A filter is a generalized subset, given by the sets that contain it: upward closed, closed under `∩`, contains `univ`.

- `F ≤ G` means `G.sets ⊆ F.sets`: the smaller the filter, the more sets.

- Examples: `𝓟 s`, `atTop`, `cofinite`, `𝓝 x`.

- `Tendsto f F G` is `map f F ≤ G`; it covers every classical limit.

- `∀ᶠ x in F, p x` is `{x | p x} ∈ F`; combine such hypotheses with `filter_upwards`.
