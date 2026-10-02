import VersoSlides
import Verso.Doc.Concrete
import Mathlib

open VersoSlides

set_option pp.rawOnError true

#doc (Slides) "Filters in Mathlib" =>

# Filters

:::fitText
A filter is a *generalized subset*.
:::

:::notes
This is the one idea of the lecture. Everything else follows from it.
Keep coming back to this sentence.
:::

# Learning goal

By the end you can

:::fragment fadeUp
- say why Mathlib defines limits through filters,
:::

:::fragment fadeUp
- write down the three filter axioms,
:::

:::fragment fadeUp
- read `Tendsto` as a single definition.
:::

# The problem

Three $`\varepsilon`-$`\delta` definitions:

- $`a_n \to l`
- $`f(x) \to l` as $`x \to x_0`
- $`f(x) \to \infty` as $`x \to \infty`

:::fragment highlightBlue
One shape: *for good enough inputs, the output lies in a given set.*
:::

:::notes
Do not read the quantifiers out loud -- the students know them.
The point is only that the three look alike.
:::

# The idea

A generalized subset $`F` of $`\alpha` is pinned down by the *actual*
sets that contain it.

:::fragment fadeUp
Newton wanted $`dx` to be a number infinitesimally close to $`0`.
A filter is how we get that back.
:::

:::notes
Stress that we never say what F *is* -- only which sets contain it.
That move is the whole trick.
:::

# The three axioms

Which sets may contain $`F`?

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

:::fragment fadeUp
`S ∈ F` morally means `F ⊆ S`.
:::

# Three filters to know

`principal s` is $`s` itself, `atTop` is *n large enough*,
`cofinite` is *all but finitely many*.

```lean -panel -stretch
open Filter
#check (principal : Set ℕ → Filter ℕ)
#check (atTop : Filter ℕ)
#check (cofinite : Filter ℕ)
```

# The payoff

One definition instead of three:

```lean -panel -stretch
open Filter in
example (f : α → β) (F : Filter α) (G : Filter β) :
    Prop :=
  Tendsto f F G
```

:::fragment highlightGreen
$`a_n \to l` is `Tendsto a atTop (nhds l)`.
:::

:::notes
Close the loop: the same definition gives sequence limits, function
limits, and limits at infinity.
:::

# In one line

:::fitText
Filter = generalized subset
:::

Three axioms. One notion of limit. The rest is notation.
