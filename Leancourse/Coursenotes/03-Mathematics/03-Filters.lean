import VersoManual
import Manual.Meta
import Leancourse.Misc.Defs
import Mathlib

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open MyDef

set_option pp.rawOnError true
set_option verso.docstring.allowMissing true

#doc (Manual) "Filters in Mathlib" =>
%%%
htmlSplit := .never
tag := "filters"
%%%

Filters are one of the most distinctive design choices in Mathlib. They
provide a unified framework for limits, neighborhoods, convergence, and
"eventually" -- replacing the many different epsilon-delta definitions
that appear in classical analysis.

The exposition below follows the pedagogical approach of Kevin Buzzard and
Bhavik Mehta in their
[Formalising Mathematics notes](https://github.com/b-mehta/formalising-mathematics-notes):
a filter is a *generalized subset*.

# Notation and naming conventions
%%%
tag := "filters-notation"
%%%

:::table +header
* + Symbol
  + Lean name
  + Reads as
  + Typed as
* + `Filter α`
  + `Filter α`
  + "filter on α"
  + (ASCII)
* + `F.sets`
  + `Filter.sets F`
  + "the sets of the filter F"
  + (ASCII)
* + `s ∈ F`
  + `s ∈ F.sets`
  + "s is a member of F" (F-large)
  + `\in`
* + `F ≤ G`
  + `LE.le F G`
  + "F is finer than G"
  + `\le`
* + `𝓟 s`
  + `Filter.principal s`
  + "the principal filter of s"
  + `\McP`
* + `⊤`
  + `Top.top`
  + "the top filter" (only Set.univ)
  + `\top`
* + `⊥`
  + `Bot.bot`
  + "the bottom filter" (every set)
  + `\bot`
* + `atTop`
  + `Filter.atTop`
  + "at top" / "going to ∞"
  + (ASCII)
* + `atBot`
  + `Filter.atBot`
  + "at bottom" / "going to −∞"
  + (ASCII)
* + `cofinite`
  + `Filter.cofinite`
  + "the cofinite filter"
  + (ASCII)
* + `nhds x`
  + `nhds x`
  + "neighborhood filter at x"
  + `\nhds` for `𝓝`
* + `𝓝 x`
  + `nhds x`
  + same as above
  + `\nhds`
* + `f ⁻¹' s`
  + `Set.preimage f s`
  + "preimage of s under f"
  + `\inv'`
* + `Filter.map f F`
  + `Filter.map f F`
  + "pushforward of F along f"
  + (ASCII)
* + `Filter.comap f G`
  + `Filter.comap f G`
  + "pullback of G along f"
  + (ASCII)
* + `Tendsto f F G`
  + `Filter.Tendsto f F G`
  + "f tends from F to G"
  + (ASCII)
* + `∀ᶠ x in F, p x`
  + `Filter.Eventually p F`
  + "eventually p, along F"
  + `\all\^f`
* + `∃ᶠ x in F, p x`
  + `Filter.Frequently p F`
  + "frequently p, along F"
  + `\ex\^f`
:::

Naming hints.

- `F ≤ G` is pronounced "F is *finer* than G": smaller filters contain
  more sets. The slogan is: the smaller the filter, the bigger its
  collection of sets.
- The prefix `mem_` (as in `mem_principal`, `mem_atTop_sets`,
  `mem_nhds_iff`) names lemmas that *characterize membership* in a
  given filter.
- `𝓟` and `𝓝` are mathematical script letters, typed `\McP` and
  `\nhds`; they are *notation*, not definitions.
- `⁻¹'` is the preimage of a set under a function (not to be confused
  with the inverse `⁻¹` of a group element); it is typed `\inv'` (or
  `\i\n\v '` in sequence).

# Motivation: why filters?
%%%
tag := "filter-motivation"
%%%

In a traditional analysis course one meets many similar-looking
definitions:

- A sequence `a : ℕ → ℝ` converges to `l` if for every `ε > 0` there
  exists `N` such that for all `n ≥ N`, `|a n - l| < ε`.
- A function `f : ℝ → ℝ` has limit `l` at `x₀` if for every `ε > 0`
  there exists `δ > 0` such that for all `x` with `0 < |x - x₀| < δ`,
  `|f x - l| < ε`.
- A function `f : ℝ → ℝ` tends to `+∞` as `x → +∞` if for every `M`
  there exists `N` such that for all `x ≥ N`, `f x ≥ M`.

All of these have the shape: "for sufficiently large/close inputs, the
output lies in a given set." Filters capture this pattern abstractly.

# Filters as generalized subsets
%%%
tag := "filter-generalized-subset"
%%%

Morally, a filter on a type `α` is a *generalized subset* of `α`.  Every
ordinary subset gives rise to a filter, but there are other filters
representing "ideas" that cannot be described by a single subset, such as
an infinitesimal neighborhood of a point in a topological space, or a
neighborhood of `∞` in a totally ordered set.  Isaac Newton wanted `dx`
to be "a real number infinitesimally close to `0`"; filters are a modern
way to recover such thoughts.

The property we want a generalized subset `F` to have is that it is
uniquely determined by the *actual* subsets which contain `F`.  If `F` is
a generalized subset of `α`, what properties should the collection of
actual subsets containing `F` have?

1. If `S` contains `F` and `S ⊆ T`, then `T` contains `F`.
2. If `S` and `T` both contain `F`, then so does `S ∩ T`.
3. The whole type `Set.univ : Set α` contains `F`.

These three axioms turn out to be enough: a filter is modelled precisely
as a collection of subsets of `α` satisfying them.

# The formal definition
%%%
tag := "filter-definition"
%%%

The Mathlib definition, rendered directly from the library:

{docstring Filter}

Some authors add a fourth axiom forbidding `∅ ∈ sets`. Mathlib does not:
this is analogous to disallowing a ring as an ideal of itself. It makes
the initial definition cleaner but introduces many awkward edge cases
later, so Mathlib keeps the "empty filter" `⊥` as a legitimate object.

If `F : Filter α` and `S : Set α`, the notation `S ∈ F` is sugar for
`S ∈ F.sets`.  Think of it as morally meaning `F ⊆ S` -- but of course
that expression does not type-check, because `F` is a filter, not a set.

The axioms are restated in the `Filter` namespace under friendlier
names, rendered here directly from Mathlib:

{docstring Filter.univ_mem}

{docstring Filter.mem_of_superset}

{docstring Filter.inter_mem}

# The order on filters
%%%
tag := "filter-order"
%%%

Filters form a partial order by `≤`.  The definition is

```
F ≤ G ↔ G.sets ⊆ F.sets
```

which looks reversed, but matches the "generalized subset" intuition: if
`F` is contained in `G` as generalized subsets, then every actual subset
containing `G` also contains `F`, so `G.sets ⊆ F.sets`.  A useful slogan:

> The smaller the filter, the more sets it has.

The API lemma is:

{docstring Filter.le_def}

# The principal filter
%%%
tag := "principal-filter"
%%%

The simplest filter is the *principal filter*, with notation `𝓟 s`.
It is the filter whose sets are exactly the supersets of `s` -- i.e.
the generalized subset corresponding to the ordinary subset `s`.

{docstring Filter.principal}

```lean
-- 𝓟 s contains exactly the supersets of s
example {α : Type*} (s t : Set α) :
    t ∈ Filter.principal s ↔ s ⊆ t :=
  Filter.mem_principal

-- Every s belongs to its own principal filter
example {α : Type*} (s : Set α) :
    s ∈ Filter.principal s :=
  Filter.mem_principal_self s

-- The principal filter on the whole space is ⊤
example {α : Type*} :
    Filter.principal (Set.univ : Set α) = ⊤ :=
  Filter.principal_univ

-- The order on principal filters matches subset inclusion
example {α : Type*} (s t : Set α) :
    Filter.principal s ≤ Filter.principal t ↔ s ⊆ t :=
  Filter.principal_mono
```

# The atTop filter
%%%
tag := "atTop-filter"
%%%

On any preorder, `Filter.atTop` is the filter of sets that contain all
sufficiently large elements.  Morally, `atTop` is a "neighborhood of
`∞`": it represents "arbitrarily large elements" even though no single
largest element exists.

{docstring Filter.atTop}

```lean
-- Characterization of membership in atTop
example (s : Set ℕ) :
    s ∈ Filter.atTop ↔ ∃ a, ∀ b, a ≤ b → b ∈ s :=
  Filter.mem_atTop_sets

example :
    {n : ℕ | n ≥ 100} ∈ (Filter.atTop : Filter ℕ) := by
  rw [Filter.mem_atTop_sets]
  exact ⟨100, fun b hb ↦ hb⟩
```

# The cofinite filter
%%%
tag := "cofinite-filter"
%%%

Another instructive example: on any type `α`, the *cofinite filter*
consists of sets whose complement is finite.

{docstring Filter.cofinite}

```lean
example (α : Type*) (s : Set α) :
    s ∈ (Filter.cofinite : Filter α) ↔ sᶜ.Finite :=
  Iff.rfl
```

This filter is a generalized subset of `α` representing "almost every
element".  On `ℕ` it in fact *coincides* with `atTop` (the lemma
`Nat.cofinite_eq_atTop`): a set omits only finitely many naturals
exactly when it contains every sufficiently large one.  On other types
the two differ, and comparing filters like these is a good way to train
the "generalized subset" intuition.

# Filter.map: the pushforward
%%%
tag := "filter-map"
%%%

Given `F : Filter α` and `m : α → β`, there is a natural way to build a
filter on `β`: a set `s : Set β` is in the pushforward if its preimage
is in `F`.  This is the filter-theoretic counterpart of the image of a
subset.

{docstring Filter.map}

```lean
example {α β : Type*} (m : α → β) (F : Filter α)
    (s : Set β) :
    s ∈ Filter.map m F ↔ m ⁻¹' s ∈ F := Iff.rfl
```

There is also a pullback:

{docstring Filter.comap}

`map` and `comap` form a Galois connection:

{docstring Filter.map_le_iff_le_comap}

# Filter.Tendsto: the general notion of limit
%%%
tag := "filter-tendsto"
%%%

With `map` in hand, the general definition of a limit is strikingly
short:

{docstring Filter.Tendsto}

Unpacking: `Tendsto f l₁ l₂` says that for every `s ∈ l₂`, the preimage
`f ⁻¹' s` is in `l₁`.  In the generalized-subset picture, it says that
`f` sends the generalized subset `l₁` into the generalized subset `l₂`.

This single definition unifies all classical limits:

:::table +header
* + Classical statement
  + Filter version
* + `aₙ → l` as `n → ∞`
  + `Tendsto a atTop (nhds l)`
* + `f(x) → l` as `x → x₀`
  + `Tendsto f (nhds x₀) (nhds l)`
* + `f(x) → l` as `x → ∞`
  + `Tendsto f atTop (nhds l)`
* + `f(x) → ∞` as `x → ∞`
  + `Tendsto f atTop atTop`
:::

```lean
-- Sanity check: Tendsto for sequences
-- is the epsilon-N definition
example (a : ℕ → ℝ) (l : ℝ) :
    Filter.Tendsto a Filter.atTop (nhds l) ↔
    ∀ ε > 0, ∃ N, ∀ n ≥ N, |a n - l| < ε := by
  rw [Metric.tendsto_atTop]
  simp [Real.dist_eq]

```

Composition: if `a → l` and `f` is continuous at `l`, then `f ∘ a → f l`:

{docstring Filter.Tendsto.comp}

# Filter.Eventually and Filter.Frequently
%%%
tag := "eventually-frequently"
%%%

Filters let us speak precisely about something being true "eventually".
`Filter.Eventually p F`, with notation `∀ᶠ x in F, p x`, is defined as
`{x | p x} ∈ F`.  Read it as: "`p` holds for generalized-almost-all `x`
with respect to `F`."

- For `F = atTop` on `ℕ`, `∀ᶠ n in atTop, p n` means "for all sufficiently large `n`, `p n`".
- For `F = nhds x₀`, `∀ᶠ x in nhds x₀, p x` means "`p` holds on a neighborhood of `x₀`".
- For `F = cofinite`, it means "`p` holds off a finite set".

The dual `Filter.Frequently p F` (notation `∃ᶠ x in F, p x`) is the
negation of `Eventually (¬ p)` and means "`p` holds on an `F`-non-negligible
set".

```lean
-- Eventually for atTop unfolds to an existential
example {p : ℕ → Prop} :
    (∀ᶠ n in Filter.atTop, p n) ↔
      ∃ N, ∀ n ≥ N, p n :=
  Filter.eventually_atTop

-- Finite conjunctions of eventually hold eventually
example {α : Type*} {F : Filter α} {p q : α → Prop}
    (hp : ∀ᶠ x in F, p x) (hq : ∀ᶠ x in F, q x) :
    ∀ᶠ x in F, p x ∧ q x :=
  hp.and hq

-- Tendsto preserves Eventually
#check @Filter.Tendsto.eventually
```

When you have several `∀ᶠ`-hypotheses and want to conclude another
`∀ᶠ`-statement pointwise, the dedicated tactic
`filter_upwards [h₁, h₂, …] with x h₁ h₂ …` intersects them and
hands you the pointwise goal:

```lean
example {α : Type*} {F : Filter α} {p q : α → Prop}
    (hp : ∀ᶠ x in F, p x) (hq : ∀ᶠ x in F, q x) :
    ∀ᶠ x in F, p x ∧ q x := by
  filter_upwards [hp, hq] with x hp hq
  exact ⟨hp, hq⟩
```

A remark on `≥`.  Lean generally prefers `≤` over `≥`, and most lemmas
are stated with `≤`.  The binder `∀ n ≥ N, ...` is a special exception
(because `∀ N ≤ n, ...` would bind `N` rather than `n`), but in bare
inequalities prefer to write `1 < n` over `n > 1`.

# A worked example: `1 / (n + 1) → 0`
%%%
tag := "filter-worked-example"
%%%

To see all of the pieces working together, let us show that
`1 / (n + 1) → 0` as `n → ∞`, using `Tendsto`, `atTop`, and `nhds 0`
in the metric setting:

```lean
example : Filter.Tendsto
    (fun n : ℕ => 1 / ((n : ℝ) + 1))
    Filter.atTop (nhds 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  -- Find N with 1/(N+1) < ε:
  -- it suffices that N + 1 > 1/ε.
  obtain ⟨N, hN⟩ := exists_nat_gt (1 / ε)
  refine ⟨N, fun n hn => ?_⟩
  have hε' : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hN' : (1 : ℝ) / ε < (n : ℝ) + 1 := by
    calc (1 : ℝ) / ε < N := hN
      _ ≤ n := by exact_mod_cast hn
      _ < (n : ℝ) + 1 := by linarith
  rw [Real.dist_eq, sub_zero, abs_of_pos (by positivity)]
  rw [div_lt_iff₀ hε']
  have : 1 < ε * ((n : ℝ) + 1) := by
    have h := (div_lt_iff₀ hε).mp hN'
    linarith [h]
  linarith
```

The structure of the proof mirrors the classical epsilon-N argument
exactly: pick `N`, then show `n ≥ N → |1 / (n+1) - 0| < ε`. The
filter language lets us *state* convergence in one line; the actual
work is still the inequality manipulation.

# Ultrafilters
%%%
tag := "ultrafilters"
%%%

An *ultrafilter* is a maximal proper filter (xxx: *proper filter* is not defined): for every set `s`, either
`s` or `sᶜ` belongs to the ultrafilter.  Ultrafilters are fundamental in
logic (they correspond to consistent complete theories) and in topology
(compactifications, nonstandard analysis).

```lean
#check Ultrafilter
#check (pure : ℕ → Ultrafilter ℕ)
```

# Why filters are better for formalization
%%%
tag := "filters-advantages"
%%%

Filters may feel abstract at first, but they pay off:

1. *Unification.*  One definition of `Tendsto` replaces dozens of
   epsilon-delta variants.
2. *Composability.*  Limits compose naturally via `Filter.Tendsto.comp`.
3. *Algebraic structure.*  Filters form a {ref "complete-lattices"}[complete lattice], so we can
   take meets and joins of families of filters and reason about them
   order-theoretically.
4. *Avoidance of partial functions.*  Instead of "the limit of `f` at
   `x`" (which may not exist), we use `Tendsto f (nhds x) (nhds l)` as
   a proposition.
5. *Smooth interaction with topology.*  The neighborhood filter
   `nhds x` is the bridge between filters and topological spaces.
