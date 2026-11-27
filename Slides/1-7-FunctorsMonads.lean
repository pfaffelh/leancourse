import VersoSlides
import Verso.Doc.Concrete
import Mathlib

open VersoSlides

set_option pp.rawOnError true

/-
Deck for the chapter "Coercions and hierarchies" (part "Lean and its
type theory"): coercions, the algebraic hierarchy, classes from
analysis (`TopologicalSpace`, `MetricSpace`, `CompleteSpace`),
managing instances. It continues chapter 1.6, deck
`1-6-Typeclasses`.
-/

namespace SlidesFunctorsMonads
#doc (Slides) "Coercions and hierarchies" =>

```css
.reveal section p { font-size: 0.8em; line-height: 1.32; margin: 0.42em 0; }
.reveal section p.key, .reveal section .key p { color: #1b91ff; }
.reveal section table { font-size: 0.62em; margin: 0.2em auto 0.4em; }
.reveal section table th,
.reveal section table td { padding: 0.18em 0.9em; }
.reveal section li { font-size: 0.8em; }
```

# Coercions and hierarchies

Lean and its type theory — chapter 7

# Coercions

A coercion: a conversion Lean inserts when a term of type `α` stands where `β` is expected. Lean finds an instance of a coercion class and inserts its function.

:::table +colHeaders
*
  * Class
  * Converts a term into ...
  * Example
*
  * `Coe` and variants
  * a term of another type
  * `ℕ → ℤ`; subtype into base type
*
  * `CoeSort`
  * a type
  * a set as a type; `b : Bool` as the type `b = true`
*
  * `CoeFun`
  * a function
  * a bundled morphism applied as `f x`
:::

:::class "key"
The term contains the function of the instance, not `Coe.coe`: `Nat.cast n`, `x.val`, `Set.Elem s`, `DFunLike.coe f`. Lean shows them as `↑n`, `↑x`, `↥s`, `⇑f`.
:::

# `Coe`: a term of another type

```
class Coe (α : semiOutParam (Sort u)) (β : Sort v) where
  coe : α → β
```

```lean -panel -stretch
structure PosNat where
  val : ℕ
  pos : 0 < val
instance : Coe PosNat ℕ := ⟨PosNat.val⟩
#check fun (p : PosNat) => (p + p : ℕ)
example (p : PosNat) : (p : ℕ) = Coe.coe p := rfl
```

- `p + p` with `p : PosNat`: Lean wants `ℕ`, finds the instance, inserts `PosNat.val`
- `Coe` is the class for coercions between your own types

# The coercion classes

```
class Coe     (α : semiOutParam (Sort u)) (β : Sort v)
class CoeTail (α : semiOutParam (Sort u)) (β : Sort v)
class CoeOut  (α : Sort u) (β : semiOutParam (Sort v))
class CoeHead (α : Sort u) (β : semiOutParam (Sort v))
-- each with the one field  coe : α → β
```

:::table +colHeaders
*
  * class
  * how often in a chain
  * example
*
  * `Coe`
  * any number
  * your own types
*
  * `CoeOut`
  * any number
  * `subtypeCoe : CoeOut (Subtype p) α`
*
  * `CoeTail`
  * once, at the end
  * `[NatCast R] → CoeTail ℕ R`
*
  * `CoeHead`
  * once, at the start
  * rare
*
  * `CoeDep`
  * alone
  * `[Decidable p] → CoeDep Prop p Bool`
:::

# Chains of coercions

Lean searches the class `CoeT α x β`: a chain `CoeHead? CoeOut* Coe* CoeTail?`, or one `CoeDep`.

```lean -panel -stretch
#check fun (p : PosNat) => (p : ℤ)
```

- `PosNat → ℕ` by `Coe`, then `ℕ → ℤ` by `CoeTail` (from `NatCast ℤ`, chapter 2.1)
- `CoeTail ℕ R` for every `R` with `NatCast R`: applied twice it would loop, so it may only end a chain

# `semiOutParam`

```
class CoeTail (α : semiOutParam (Sort u)) (β : Sort v)
instance [CoeTail β γ] [CoeHTC α β] : CoeHTCT α γ
```

- the instance builds chains (Lean's core, `Init/Coe.lean`); for `PosNat → ℤ` the middle type `β` is unknown
- normally the search refuses a subgoal with an unknown argument
- `semiOutParam` allows `CoeTail ?β ℤ`: each instance supplies its `β`; from `NatCast ℤ` comes `β = ℕ`, then `Coe PosNat ℕ`
- so `Coe`, `CoeTail` are found backwards from the target, `CoeOut`, `CoeHead` forwards from the source

# The condition of `semiOutParam`

Every instance must fix the marked argument:

```
instance {α : Type} : Coe α ℕ := ⟨fun _ => 0⟩
-- error: instance does not provide concrete values
--   for (semi-)out-params
--   Coe ?α ℕ
```

- `outParam` (1.6): always found by the search, as `γ` in `HMul α β γ`
- `semiOutParam`: given, as in `Coe PosNat ℕ`, or found, as in `CoeTail ?β ℤ`

# `CoeDep`

```
class CoeDep (α : Sort u) (x : α) (β : Sort v) where
  coe : β
instance decPropToBool (p : Prop) [Decidable p] :
    CoeDep Prop p Bool := ⟨decide p⟩
```

```lean -panel -stretch
#check fun (n : ℕ) => (n < 5 : Bool)
```

- whether there is an instance depends on the term `x`, not only on its type: a `Prop` becomes a `Bool` only if it is decidable, so the instance needs `p` itself

# `CoeSort`: a type

```
class CoeSort (α : Sort u) (β : outParam (Sort v)) where
  coe : α → β
```

```lean -panel -stretch
structure PointedType where
  carrier : Type
  pt : carrier
instance : CoeSort PointedType Type :=
  ⟨PointedType.carrier⟩
example (X : PointedType) : X := X.pt
example (s : Set ℕ) : (s : Type) = {x // x ∈ s} := rfl
example (b : Bool) (h : b) : b = true := h
```

- `x : X` needs a type after the colon; Lean inserts `X.carrier`
- the same for a set `s` or a subgroup `H` used as a type

# `CoeFun`: a function

```
class CoeFun (α : Sort u) (γ : outParam (α → Sort v)) where
  coe : (f : α) → γ f
```

```lean -panel -stretch
structure AffineFn where
  a : ℝ
  b : ℝ
instance : CoeFun AffineFn (fun _ => ℝ → ℝ) :=
  ⟨fun f x => f.a * x + f.b⟩
example : (⟨3, 1⟩ : AffineFn) 2 = 7 := by
  show (3 : ℝ) * 2 + 1 = 7
  norm_num
```

- `f 2` with a structure `f`: Lean inserts the function of the instance
- `γ f`: the type of the function may depend on `f`

# Bundled maps

- `f : ℕ →+ ℕ` is a structure: a function and the proofs that it preserves `0` and `+`
- `f n` works through the class `DFunLike` (Mathlib); `coe_injective`: a map is determined by its function

```
class DFunLike (F : Sort*) (α : outParam (Sort*))
    (β : outParam (α → Sort*)) where
  coe : F → (a : α) → β a
  coe_injective : Function.Injective coe
instance DFunLike.toCoeFun [DFunLike F α β] :
    CoeFun F (fun _ => (a : α) → β a) := ⟨DFunLike.coe⟩
```

```lean -panel -stretch
example (f : ℕ →+ ℕ) (n : ℕ) : f n = DFunLike.coe f n := rfl
```

:::class "key"
Each kind of map registers `DFunLike`; one generic `CoeFun` instance serves them all.
:::

# Where the arrow goes

```lean -panel -stretch
def sub1 (n : ℕ) : ℤ := (n - 1 : ℤ)
def sub1' (n : ℕ) : ℤ := ((n - 1 : ℕ) : ℤ)
#eval (sub1 0, sub1' 0)
def q (a b : ℕ) : ℚ := (a / b : ℚ)
def q' (a b : ℕ) : ℚ := ((a / b : ℕ) : ℚ)
#eval (q 7 2, q' 7 2)
```

- Lean elaborates from the outside in: `(n - 1 : ℤ)` is first `_ - _ : ℤ`, then `n : ℤ` needs a coercion: `↑n - 1`
- in `((n - 1 : ℕ) : ℤ)` the subtraction is in `ℕ`: `↑(n - 1)`, which is `0` for `n = 0`
- the infoview shows where the `↑` sits

# More pitfalls

```lean -panel -stretch
#check fun (n : ℕ) => ↑n

example (n : ℕ) (h : n < 5) : (n : ℤ) < 5 := by
  exact_mod_cast h
```

- `↑n` without a target type does nothing: `fun n => n : ℕ → ℕ`
- `exact h` fails: `n < 5` is not `↑n < 5`; `exact_mod_cast` (chapter 2.1)
- `ring` and `linarith` treat `↑(n - 1)` as an unknown; `push_cast` moves `↑` inwards (2.1)
- how `(n : ℤ)` calls the coercion: chapter 1.8

# Casts: from `ℕ` to `ℝ`

```lean -panel -stretch
example : ((0 - 1 : ℕ) : ℝ) = 0 := by norm_num
example : ((0 : ℕ) : ℝ) - 1 = -1 := by norm_num
example (n : ℕ) :
    ((n + 1 : ℕ) : ℝ) ^ 2 = (n : ℝ) ^ 2 + 2 * n + 1 := by
  push_cast
  ring
```

- the cast is `Nat.cast`, from `NatCast ℝ` via `CoeTail`; casts: coercions along `ℕ → ℤ → ℚ → ℝ → ℂ`
- `((n - 1 : ℕ) : ℝ)` subtracts in `ℕ`, `(n : ℝ) - 1` in `ℝ`
- `↑(n + 1) = ↑n + 1` is not `rfl`; `ring` fails, `push_cast` moves the `↑` inwards
- `#eval` does not work on `ℝ`

# Casts go only one way

```lean -panel -stretch
open NNReal in
example (x : ℝ≥0) : (x : ℝ) = x.val := rfl
example : ⌊(-2.5 : ℝ)⌋₊ = 0 := by norm_num
example : (-3 : ℝ).toNNReal = 0 := by simp
```

- a cast exists where no value is lost: `ℕ → ℝ`; `ℝ≥0 → ℝ` forgets the proof of `0 ≤ x`
- `(x : ℕ)` for `x : ℝ` is a type error
- the way back is a function with a junk value: `⌊x⌋₊`, `x.toNNReal`

:::class "key"
All casts, including `ℝ≥0∞`, and the tactics: chapter 2.1.
:::

# Hierarchies with `extends`

```
class Group (α : Type) extends Monoid α where
  inv : α → α
  inv_mul_cancel : ∀ a : α, inv a * a = 1
```

```lean -panel -stretch
example (α : Type) [CommRing α] : AddCommGroup α :=
  inferInstance
#synth AddCommGroup ℤ
```

- `extends` makes `Monoid α` a field; the projection to it is an instance (the algebra: chapter 2.5)
- `mul_comm` is stated once, for `CommMagma`
- two paths to the same class must agree: else a _diamond_

# `TopologicalSpace`: a class with data

```
class TopologicalSpace (X : Type u) where
  IsOpen : Set X → Prop
  isOpen_univ : IsOpen Set.univ
  isOpen_inter : ∀ s t : Set X,
    IsOpen s → IsOpen t → IsOpen (s ∩ t)
  isOpen_sUnion : ∀ S : Set (Set X),
    (∀ t ∈ S, IsOpen t) → IsOpen (⋃₀ S)
```

- one data field, `IsOpen`, and three axioms: the textbook definition
- `[TopologicalSpace X]` reads "`X` with a topology"; the instance fixes which one
- open sets, continuity, limits: chapters 2.6 and 2.7

# `MetricSpace`

```
class PseudoMetricSpace (α : Type u) extends Dist α where
  dist_self : ∀ x : α, dist x x = 0
  dist_comm : ∀ x y : α, dist x y = dist y x
  dist_triangle : ∀ x y z : α,
    dist x z ≤ dist x y + dist y z
  toUniformSpace : UniformSpace α := .ofDist dist …
class MetricSpace (α : Type u)
    extends PseudoMetricSpace α where
  eq_of_dist_eq_zero : ∀ {x y : α}, dist x y = 0 → x = y
```

- `Pseudo`: `dist x y = 0` is allowed for `x ≠ y`
- `#synth TopologicalSpace ℚ` gives `PseudoMetricSpace.toUniformSpace.toTopologicalSpace`: the `extends` chain down to the topology

# The topology is a field

```
toUniformSpace : UniformSpace α := .ofDist dist …
```

- the uniform structure, and with it the topology, is a *field* of `PseudoMetricSpace` with a default value, not a function of `dist` computed afterwards
- an instance may set the field to a topology that already exists
- `α × β`: the product metric and the product topology give the same open sets, but are not equal by definition. The product metric takes the product structure as its field, so both paths give the same instance: no diamond

# `CompleteSpace`: a property as a class

```
class CompleteSpace (α : Type u) [UniformSpace α] : Prop where
  complete : ∀ {f : Filter α}, Cauchy f → ∃ x, f ≤ nhds x
```

```lean -panel -stretch
#synth CompleteSpace ℝ
example (u : ℕ → ℝ) (hu : CauchySeq u) :
    ∃ x, Filter.Tendsto u Filter.atTop (nhds x) :=
  cauchySeq_tendsto_of_complete hu
```

- in `Prop`, like `Fact`: no data, only whether it holds; it sits on top of `[UniformSpace α]`
- stated with Cauchy filters (chapter 2.6); for a metric space the same as "Cauchy sequences converge"
- `#synth CompleteSpace ℚ` fails: there is no instance

# Class or not?

```
structure Continuous [TopologicalSpace X] [TopologicalSpace Y]
    (f : X → Y) : Prop where
  isOpen_preimage : ∀ s, IsOpen s → IsOpen (f ⁻¹' s)
```

:::table +colHeaders
*
  * declaration
  * kind
  * how Lean gets it
*
  * `TopologicalSpace X`, `MetricSpace X`
  * class with data
  * instance search, from the type
*
  * `CompleteSpace X`, `CompactSpace X`
  * class in `Prop`
  * instance search, from the type
*
  * `Continuous f`
  * structure in `Prop`
  * a proof, for each `f`
*
  * `IsCompact s`
  * `def`
  * a proof, for each `s`
:::

:::class "key"
A class is for what follows from the type alone. `Continuous f` depends on the term `f`, so it is proved, not searched.
:::

# New type, class, or structure?

:::table +colHeaders
*
  * situation
  * means
  * examples
*
  * new elements
  * new type
  * `PosNat`, `ℚ`, `ℂ`
*
  * one canonical structure per type
  * class
  * `Group`, `TopologicalSpace`
*
  * many at once on one type
  * `structure`, objects are terms
  * `Filter α`, `Subgroup G`, `Measure α`
*
  * same elements, second structure
  * type synonym, own instance
  * `Lex α`, `αᵒᵈ`, `WithLp p V`
*
  * property of a term
  * `structure`/`def` in `Prop`
  * `Continuous f`, `IsCompact s`
:::

:::class "key"
The question: how many such structures are needed on the same type at the same time?
:::

# `Filter` is a structure

```lean -panel -stretch
#check (Filter.atTop : Filter ℕ)
#check (Filter.cofinite : Filter ℕ)
example : (⊥ : TopologicalSpace ℕ) ≤ ⊤ := bot_le
```

- several filters on `ℕ` at once; `Tendsto u atTop (𝓝 x)` uses two
- a class would mean: the type determines the filter
- `TopologicalSpace` is a class, since a type usually has one topology; to compare topologies, the class is an ordinary type
- a second instance on the same elements needs a type synonym: `Lex α` (1.6), `αᵒᵈ`

# Managing instances

- `instance (priority := 2000)`: tried before the default `1000`
- Lean takes the first solution it finds
- `local instance`: until the end of the section
- `scoped instance`: inside its namespace, or after `open`
- `@[default_instance]`: a bare `2` defaults to `ℕ`
- "failed to synthesize": an instance is missing

# Summary

- coercions are instances of `Coe`, `CoeSort`, `CoeFun`
- the algebraic hierarchy is a chain of `extends`
- `TopologicalSpace`, `MetricSpace`: classes with data; `CompleteSpace`: a class in `Prop`; `Continuous`: no class
- class if the type determines the structure; `structure` if many are needed at once (`Filter`)
