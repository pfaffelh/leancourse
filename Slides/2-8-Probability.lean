import VersoSlides
import Verso.Doc.Concrete
import Mathlib

open VersoSlides

set_option pp.rawOnError true

/-
Deck for the chapter "Monads and Probability Mass Functions" of part 2
(Mathematics), the last lecture of the course. It follows the chapter
section by section: monads in mathematics (sets, finite sets, filters),
then probability mass functions (definition, `pure`, `bind`, `map`,
`join`, the `Monad PMF` instance, concrete distributions, beyond
`PMF`s).
-/

namespace SlidesProbability
open scoped ENNReal Topology

#doc (Slides) "Monads and probability" =>

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

# Monads and probability

Mathematics — chapter 8

:::class "key"
A discrete distribution is built from others with `pure`, `map` and `bind`. In Mathlib, `PMF` is a monad.
:::

# Monads

:::table +colHeaders +rowSeps
*
  * operation
  * type
  * for `List`
*
  * `pure`
  * `α → m α`
  * `[a]`
*
  * `map`, `f <$> x`
  * `(α → β) → m α → m β`
  * apply `f` to each entry
*
  * `bind`, `x >>= f`
  * `m α → (α → m β) → m β`
  * apply `f`, concatenate
:::

Laws: `pure_bind`, `bind_pure`, `bind_assoc`. A `do`-block is a chain of `>>=`.

:::class "key"
`map f x = x >>= (pure ∘ f)` and `join = bind id`: `pure` and `bind` determine the rest.
:::

# Monads in mathematics

::::class "small"
:::table +colHeaders +rowSeps
*
  * type
  * `pure a`
  * `map f`
  * `bind s f`
*
  * `Set α`
  * `{a}`
  * the image `f '' s`
  * the union `⋃ a ∈ s, f a`
*
  * `Finset α`
  * `{a}`
  * `s.image f`
  * `s.biUnion f`
*
  * `Filter α`
  * `𝓟 {a}`
  * `Filter.map f F`
  * `Filter.bind F f`
*
  * `PMF α`
  * the Dirac measure at `a`
  * the image distribution
  * the mixture of the `f a`, weighted by `s`
:::
::::

:::class "key"
`Set`, `Filter` and `PMF` are functors without conditions. Only `PMF` is a monad by a global instance.
:::

# Sets

```lean -panel -stretch
example (f : ℕ → ℕ) (s : Set ℕ) : f <$> s = f '' s := rfl

section
attribute [local instance] Set.monad

def setPairs : Set (ℕ × ℕ) := do
  let x ← ({1, 2, 3} : Set ℕ)
  let y ← ({10, 20} : Set ℕ)
  return (x, y)

example : (3, 10) ∈ setPairs := by simp [setPairs]
end
```

`Set.monad` is not an instance: sets have no computational content, and a global `Monad Set` would make `do` look like a program.

# Finite sets

```lean -panel -stretch
example : ({1, 2} : Finset ℕ).biUnion (fun n => {n, 10 * n})
    = {1, 2, 10, 20} := by
  decide
```

A finite set has no duplicates, so the elements `f a` must be compared: `Finset.biUnion` needs `[DecidableEq β]`, and `Finset.instMonad` needs `[(P : Prop) → Decidable P]`.

:::class "key"
`Finset` is a monad only with `classical` (in a proof) or `open Classical in` (in a definition). In practice: `Finset.image` and `Finset.biUnion`.
:::

# Filters

`Filter.map f F` is the pushforward: `t ∈ Filter.map f F ↔ f ⁻¹' t ∈ F`.

```lean -panel -stretch
example (f : ℕ → ℕ) (F : Filter ℕ) :
    f <$> F = Filter.map f F := rfl
example (f : ℕ → ℕ) (F G : Filter ℕ) :
    Filter.Tendsto f F G ↔ Filter.map f F ≤ G := Iff.rfl
```

`pure a` is the principal filter `𝓟 {a}`: it contains the sets that contain `a`.

`Filter.monad` is not an instance. `Filter` has a global `<*>`, given by `Filter.seq`; a global `Monad Filter` would bring a second `<*>`, derived from `bind`, and the two differ: a diamond.

:::class "key"
A limit is a statement about `map`.
:::

# Probability mass functions

```
def PMF (α : Type u) : Type u :=
  { f : α → ℝ≥0∞ // HasSum f 1 }
```

`HasSum f 1`: the finite sums `∑ a ∈ s, f a` tend to `1` as `s` grows through the finite sets: `Tendsto … atTop (𝓝 1)` on `Finset α`. `∑' a, f a` is the value of the sum (`0` if not summable).

```lean -panel -stretch
example (f : ℕ → ℝ≥0∞) (a : ℝ≥0∞) :
    HasSum f a ↔ Filter.Tendsto
      (fun s : Finset ℕ => ∑ b ∈ s, f b)
      Filter.atTop (𝓝 a) :=
  Iff.rfl
```

:::class "key"
A `PMF` is a function with sum `1`, the sum a limit along `atTop` on finite sets (chapter 2.6).
:::

# Mass and support

```lean -panel -stretch
example {α : Type} (p : PMF α) : ∑' a, p a = 1 :=
  p.tsum_coe
example {α : Type} (p : PMF α) : p.support.Countable :=
  p.support_countable
```

`p a : ℝ≥0∞` is the mass at `a`, and `p.support = {a | p a ≠ 0}`.

:::class "key"
The support is countable and there is no σ-algebra: an expectation is the sum `∑' a, p a * g a`.
:::

# `pure`: the Dirac distribution

```lean -panel -stretch
example : (PMF.pure (0 : ℕ)) 0 = 1 :=
  PMF.pure_apply_self 0
example (n : ℕ) (h : n ≠ 0) : (PMF.pure (0 : ℕ)) n = 0 :=
  PMF.pure_apply_of_ne 0 n h
example {α : Type} (a : α) : (PMF.pure a).support = {a} :=
  PMF.support_pure a
```

Mass `1` at `a`, mass `0` elsewhere.

:::class "key"
With the type given, `(pure a : PMF α)` is `PMF.pure a` (`rfl`). Write `PMF.pure` when the type is not clear.
:::

# `bind`: composing distributions

Draw `a` according to `p`, then `b` according to `f a`.

```lean -panel -stretch
example {α β : Type} (p : PMF α) (f : α → PMF β) (b : β) :
    (p.bind f) b = ∑' a, p a * (f a) b :=
  PMF.bind_apply p f b
example {α β : Type} (p : PMF α) (f : α → PMF β) :
    (p.bind f).support = ⋃ a ∈ p.support, (f a).support :=
  PMF.support_bind p f
```

:::class "key"
The probability of `b` is the average of `(f a) b`, weighted by `p`.
:::

# The monad laws for `PMF`

```lean -panel -stretch
section
variable {α β γ : Type}
example (a : α) (f : α → PMF β) :
    (PMF.pure a).bind f = f a := PMF.pure_bind a f
example (p : PMF α) : p.bind PMF.pure = p :=
  PMF.bind_pure p
example (p : PMF α) (f : α → PMF β) (g : β → PMF γ) :
    (p.bind f).bind g = p.bind (fun a => (f a).bind g) :=
  PMF.bind_bind p f g
end
```

:::class "key"
The monad laws, for `PMF`. No measurability appears.
:::

# `map`: the image distribution

```lean -panel -stretch
example {α β : Type} (f : α → β) (p : PMF α) :
    p.bind (PMF.pure ∘ f) = p.map f :=
  PMF.bind_pure_comp f p
-- the if b = f a needs DecidableEq β
open Classical in
example {α β : Type} (f : α → β) (p : PMF α) (b : β) :
    (p.map f) b = ∑' a, if b = f a then p a else 0 :=
  PMF.map_apply f p b
```

`(p.map f) b` is the mass that `p` puts on `f ⁻¹' {b}`. `p.map f` is defined for every function `f`: no measurability hypothesis.

:::class "key"
`map` is `bind` composed with `pure`, as for every monad.
:::

# The functor laws

```lean -panel -stretch
section
variable {α β γ : Type}
example (p : PMF α) : p.map id = p := PMF.map_id p
example (f : α → β) (g : β → γ) (p : PMF α) :
    (p.map f).map g = p.map (g ∘ f) := PMF.map_comp f p g
example (f : α → β) (a : α) :
    (PMF.pure a).map f = PMF.pure (f a) := PMF.pure_map f a
example (p : PMF α) (f : α → β) (q : β → PMF γ) :
    (p.map f).bind q = p.bind (q ∘ f) := PMF.bind_map p f q
end
```

:::class "key"
Each one is a calculation with `bind` and `pure`.
:::

# `join`: a distribution of distributions

```lean -panel -stretch
noncomputable def pmfJoin {α : Type} (P : PMF (PMF α)) :
    PMF α :=
  P.bind id

example {α : Type} (p : PMF α) : pmfJoin (PMF.pure p) = p :=
  PMF.pure_bind p id
example {α : Type} (p : PMF α) :
    pmfJoin (p.map PMF.pure) = p := by
  rw [pmfJoin, PMF.bind_map]
  exact PMF.bind_pure p
```

:::class "key"
Mathlib has no `PMF.join`; the generic `joinM` (= `bind · id`) works for every monad.
:::

# The `Monad PMF` instance

```lean -panel -stretch
#synth Monad PMF
example {α β : Type} (p : PMF α) (f : α → PMF β) :
    p >>= f = p.bind f := rfl

noncomputable example (die : PMF (Fin 6)) : PMF ℕ := do
  let x ← die
  let y ← die
  pure (x.val + y.val + 2)
```

The `do`-block is `die >>= fun x => die >>= fun y => pure (x.val + y.val + 2)`, and `>>=` on `PMF` is `PMF.bind`.

:::class "key"
Two dice, summed: the `do`-block reads as the description of the experiment.
:::

# Concrete distributions

```
PMF.uniformOfFintype α : PMF α  -- α finite, nonempty
PMF.uniformOfFinset s  : s.Nonempty → PMF α
PMF.ofFintype f        : ∑ a, f a = 1 → PMF α
```

```lean -panel -stretch
example : PMF.uniformOfFintype Bool true = 1 / 2 := by
  simp [PMF.uniformOfFintype_apply]
```

:::class "key"
A fair coin: mass `1 / 2` on each side.
:::

# Beyond `PMF`s

Continuous distributions (uniform on `[0, 1]`, normal) are measures `Measure α` on a σ-algebra `MeasurableSpace α`, not part of this course. `PMF.toMeasure` turns a `PMF` into one.

`PMF.bernoulli` and `PMF.binomial` are deprecated; their successors are measures.

:::class "key"
Discrete probability stays inside `PMF`: no σ-algebra, no measurability.
:::

# What the semester covered

Part 1 described Lean's type theory: functions, inductive types, structures, recursion, quotients, the rules of the kernel, typeclasses.

Part 2 read Mathlib with it: numbers, sets, foundations, orders, algebra, filters and, today, probability; topology as reading.

The same few type formers carry all of part 2.

# Summary

- `Set`, `Finset`, `Filter` and `PMF` have `pure`, `map`, `bind`; only `PMF` is a monad by a global instance.
- `Set.monad` is local, `Finset` needs decidable equality, `Filter.monad` clashes with `Filter.seq`.
- `PMF α` is a function `α → ℝ≥0∞` with sum `1`; its support is countable.
- `PMF.pure`, `bind`, `map` and `join = bind id` satisfy the monad and functor laws, with no measurability.
- `do`-notation describes a random experiment; measures take over for continuous distributions.
