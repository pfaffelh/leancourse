import VersoManual
import Manual.Meta
import Leancourse.Markup
import Mathlib

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open MyDef

set_option pp.rawOnError true

#doc (Manual) "Coercions and hierarchies" =>
%%%
htmlSplit := .never
tag := "functors-monads"
%%%

This chapter continues {ref "typeclasses"}[chapter 1.6] with two uses of typeclasses: coercions, which convert terms between types, and hierarchies of classes built with `extends`, with examples from algebra and analysis.

The [slides](slides/1-7-functors-monads/) for this chapter follow it section by section.

# Coercions
%%%
tag := "coercions"
%%%

A *coercion* is a conversion Lean inserts automatically when a term of one type appears where another is expected, such as a `ℕ` where a `ℤ` is wanted. Mathematically there is nothing to it; in Lean it is a frequent source of goals that look right and do not close. Coercions are instances of a handful of classes, so instance resolution drives them: on a mismatch Lean searches an instance and inserts its function, written `↑`. How exactly `(n : ℤ)` triggers the search is in {ref "coercion-elaboration"}[chapter 1.8].

There are three kinds, according to *what* the target is:

:::table (align := left) +header
* + Class
  + Converts a term into ...
  + Example
* + `Coe` and its variants
  + ... a term of another type
  + `ℕ → ℤ`; a subtype into its base type
* + `CoeSort`
  + ... a *type* (where a `Sort` is expected)
  + a set as a type; `b : Bool` as the type `b = true`
* + `CoeFun`
  + ... a *function* (in applied position)
  + a bundled morphism `f` applied as `f x`
:::

The term Lean builds does not contain `Coe.coe`. The instance is unfolded at once, and what remains is the function inside it: `Nat.cast n`, `x.val`, `Set.Elem s`, `DFunLike.coe f`. These functions carry the attribute `@[coe]`, and Lean prints them as `↑n`, `↑x`, `↥s` and `⇑f`.

## `Coe`
%%%
number := false
tag := "coe-class"
%%%

```
class Coe (α : semiOutParam (Sort u)) (β : Sort v) where
  coe : α → β
```

`Coe α β` turns a term of `α` into a term of `β`. It is the class to use for coercions between one's own types:

```lean
structure PosNat where
  val : ℕ
  pos : 0 < val

instance : Coe PosNat ℕ := ⟨PosNat.val⟩

def doublePos (p : PosNat) : ℕ := p + p
#print doublePos
-- fun p => p.val + p.val
example (p : PosNat) : (p : ℕ) = Coe.coe p := rfl
```

In `p + p` Lean expects a natural number, finds `p : PosNat`, finds the instance and inserts `PosNat.val`. `#print` shows no trace of `Coe.coe`.

## Chains of coercions
%%%
number := false
tag := "coercion-chains"
%%%

`Coe` has four relatives. They have the same single field `coe : α → β` and differ in how they may be chained:

```
class Coe     (α : semiOutParam (Sort u)) (β : Sort v)
class CoeTail (α : semiOutParam (Sort u)) (β : Sort v)
class CoeOut  (α : Sort u) (β : semiOutParam (Sort v))
class CoeHead (α : Sort u) (β : semiOutParam (Sort v))
class CoeDep  (α : Sort u) (x : α) (β : Sort v)
```

For a coercion from `α` to `β`, Lean searches an instance of `CoeT α x β`. Such an instance is either one `CoeDep`, or a chain `CoeHead? CoeOut* Coe* CoeTail?`: at most one `CoeHead` at the start, any number of `CoeOut` and then of `Coe`, at most one `CoeTail` at the end.

:::table (align := left) +header
* + class
  + in a chain
  + example
* + `Coe`
  + any number
  + one's own types
* + `CoeOut`
  + any number
  + `subtypeCoe : CoeOut (Subtype p) α`
* + `CoeTail`
  + once, at the end
  + `[NatCast R] → CoeTail ℕ R`
* + `CoeHead`
  + once, at the start
  + rare
* + `CoeDep`
  + alone
  + `[Decidable p] → CoeDep Prop p Bool`
:::

`semiOutParam` marks the side that the search finds: `Coe` and `CoeTail` work back from the target `β`, `CoeOut` and `CoeHead` forward from the source `α`. `CoeTail ℕ R` exists for every `R` with a `NatCast R` (chapter 2.1); applied twice it would loop, so it may only end a chain. A chain of two steps:

```lean
def posToInt (p : PosNat) : ℤ := p
#print posToInt
-- fun p => ↑p.val
```

First `Coe PosNat ℕ`, then `CoeTail ℕ ℤ`.

`CoeDep` differs from the others: whether there is an instance depends on the term `x`, not only on its type. A proposition becomes a `Bool` only if it is decidable:

```
class CoeDep (α : Sort u) (x : α) (β : Sort v) where
  coe : β

instance decPropToBool (p : Prop) [Decidable p] :
    CoeDep Prop p Bool := ⟨decide p⟩
```

```lean
def isSmallNat (n : ℕ) : Bool := n < 5
#print isSmallNat
-- fun n => decide (n < 5)
```

## `CoeSort`
%%%
number := false
tag := "coesort-class"
%%%

```
class CoeSort (α : Sort u) (β : outParam (Sort v)) where
  coe : α → β
```

`CoeSort` lets a term stand in for a *type*. It is used where a type is expected, after a colon or around an arrow. A structure that carries a type as a field is the typical case:

```lean
structure PointedType where
  carrier : Type
  pt : carrier

instance : CoeSort PointedType Type :=
  ⟨PointedType.carrier⟩

example (X : PointedType) : X := X.pt
```

In `(X : PointedType) : X`, Lean needs a type after the colon and inserts `X.carrier`. The same happens for a set `s : Set α`, which becomes the subtype of its members, and for `b : Bool`, which becomes the proposition `b = true`:

```lean
example (s : Set ℕ) : (s : Type) = {x // x ∈ s} := rfl
example (b : Bool) (h : b) : b = true := h
```

## `CoeFun`
%%%
number := false
tag := "coefun-class"
%%%

```
class CoeFun (α : Sort u) (γ : outParam (α → Sort v)) where
  coe : (f : α) → γ f
```

`CoeFun` lets a term be applied like a function. The type of the function, `γ f`, may depend on `f`. An affine map `x ↦ a x + b`, stored as its two coefficients:

```lean
structure AffineFn where
  a : ℝ
  b : ℝ

instance : CoeFun AffineFn (fun _ => ℝ → ℝ) :=
  ⟨fun f x => f.a * x + f.b⟩

example : (⟨3, 1⟩ : AffineFn) 2 = 7 := by
  show (3 : ℝ) * 2 + 1 = 7
  norm_num
```

In Mathlib, a homomorphism `f : ℕ →+ ℕ` is a structure carrying the function together with the proofs that it preserves `0` and `+`; it is still written `f n`. Mathlib does not write a `CoeFun` instance for each kind of map. Each kind of map registers an instance of the class `DFunLike`, and one generic `CoeFun` instance serves them all ({ref "representation-pitfalls"}[How an object is represented]):

```
class DFunLike (F : Sort*) (α : outParam (Sort*))
    (β : outParam (α → Sort*)) where
  coe : F → (a : α) → β a
  coe_injective : Function.Injective coe

instance DFunLike.toCoeFun [DFunLike F α β] :
    CoeFun F (fun _ => (a : α) → β a) := ⟨DFunLike.coe⟩
```

The field `coe_injective` says that a map is determined by its function.

```lean
example (f : ℕ →+ ℕ) (n : ℕ) : f n = DFunLike.coe f n := rfl
```

## Pitfalls
%%%
number := false
tag := "coercion-pitfalls"
%%%

Lean elaborates from the outside in. In `(n - 1 : ℤ)` it first sees `_ - _ : ℤ`, so the subtraction is in `ℤ`, and only then needs `n : ℤ`; the result is `↑n - 1`. In `((n - 1 : ℕ) : ℤ)` the subtraction is in `ℕ` and the coercion comes last: `↑(n - 1)`, which is `0` for `n = 0`. Division behaves the same way:

```lean
def predInt (n : ℕ) : ℤ := (n - 1 : ℤ)
def predInt' (n : ℕ) : ℤ := ((n - 1 : ℕ) : ℤ)
#eval (predInt 0, predInt' 0)     -- (-1, 0)
def ratDiv (a b : ℕ) : ℚ := (a / b : ℚ)
def ratDiv' (a b : ℕ) : ℚ := ((a / b : ℕ) : ℚ)
#eval (ratDiv 7 2, ratDiv' 7 2)   -- (7/2, 3)
```

The infoview shows where the `↑` sits. Three further traps:

* `↑n` without a target type does nothing: `def noTarget (n : ℕ) := ↑n` has type `ℕ → ℕ`.
* A hypothesis `h : n < 5` does not prove `(n : ℤ) < 5` by `exact h`: the two statements differ by a `↑`. `exact_mod_cast h` does ({ref "number-casts"}[chapter 2.1]).
* `ring` and `linarith` treat `↑(n - 1)` as an unknown; `push_cast` moves the `↑` inwards first.

```lean
example (n : ℕ) (h : n < 5) : (n : ℤ) < 5 := by
  exact_mod_cast h
```

Coercions keep statements readable: you write `n + r` for `n : ℕ` and `r : ℝ`, and Lean reads it as `↑n + r`. Coercions between number types along `ℕ → ℤ → ℚ → ℝ → ℂ` are called *casts*. A goal can fill with `↑`s that block tactics like `ring` or `linarith`. Which casts there are, the lemmas that move them, and the tactics `push_cast`, `norm_cast` and `exact_mod_cast` are in {ref "number-casts"}[Casts] in chapter 2.1, once the number types are built.

# Hierarchies with `extends`
%%%
tag := "algebraic-hierarchy"
%%%

Mathlib's algebraic structures are typeclasses, and each one `extends` the weaker structures below it. Simplified:

```
class Group (α : Type) extends Monoid α where
  inv : α → α
  inv_mul_cancel : ∀ a : α, inv a * a = 1
```

`extends` makes `Monoid α` a field of `Group α`, and the projection (in the simplified version `Group.toMonoid`; in Mathlib `Group.toDivInvMonoid`, then `DivInvMonoid.toMonoid`) is registered as an instance. So from `[CommRing α]`, instance resolution reaches `Add α`, `Mul α` and `AddCommGroup α` by walking the `extends` chain:

```lean
example (α : Type) [CommRing α] : AddCommGroup α :=
  inferInstance

#synth AddCommGroup ℤ
```

That is what lets `mul_comm` be stated once, for `CommMagma`, and hold for `ℕ`, `ℝ`, polynomial rings and matrix rings alike. When two paths lead to the same class, they must give the same instance; when they do not, the result is a *diamond* ({ref "typeclass-diamonds"}[Typeclass diamonds] in the appendix).

Which structures there are and how to move between them is {ref "algebraic-hierarchy-mathlib"}[a chapter of its own] in the Mathematics part.

# Classes from analysis
%%%
tag := "analysis-classes"
%%%

The classes of topology and analysis follow the same patterns as the algebraic ones. They come in chapters {ref "filters"}[2.6] and {ref "topology"}[2.7]; here only their declarations matter. `Filter`, `Cauchy` and `nhds` in them are explained there.

*A class with data.* A topology on `X` is the set of open sets, together with three axioms:

```
class TopologicalSpace (X : Type u) where
  IsOpen : Set X → Prop
  isOpen_univ : IsOpen Set.univ
  isOpen_inter : ∀ s t : Set X,
    IsOpen s → IsOpen t → IsOpen (s ∩ t)
  isOpen_sUnion : ∀ S : Set (Set X),
    (∀ t ∈ S, IsOpen t) → IsOpen (⋃₀ S)
```

This is the textbook definition. A hypothesis `[TopologicalSpace X]` reads "`X` with a topology", and the instance fixes which topology.

*A hierarchy with defaults.* A metric space is built in two steps (simplified; Mathlib has further fields with default values):

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

In a *pseudo*metric space, `dist x y = 0` is allowed for `x ≠ y`. `UniformSpace` extends `TopologicalSpace`, so instance search reaches the topology of `ℚ` along the `extends` chain:

```lean
/--
info: PseudoMetricSpace.toUniformSpace.toTopologicalSpace
-/
#guard_msgs in
#synth TopologicalSpace ℚ
```

The uniform structure, and with it the topology, is a *field* of `PseudoMetricSpace` with a default value. It is not a function of `dist` computed afterwards. An instance may therefore set the field to a structure that already exists. On `α × β`, the product metric (the maximum of the two distances) and the product topology give the same open sets, but they are not equal by definition. Mathlib's product metric takes the product structure as its field, so both paths give the same instance. Without this there would be a {ref "typeclass-diamonds"}[diamond].

*A property as a class.* Completeness is a class in `Prop`, like {ref "fact"}[`Fact`]. It carries no data and sits on top of a uniform structure:

```
class CompleteSpace (α : Type u) [UniformSpace α] : Prop where
  complete : ∀ {f : Filter α}, Cauchy f → ∃ x, f ≤ nhds x
```

It is stated with Cauchy filters. For a metric space this is the same as "every Cauchy sequence converges" (`Metric.complete_of_cauchySeq_tendsto`). Instance search finds it for `ℝ`, not for `ℚ`:

```lean
#synth CompleteSpace ℝ

example (u : ℕ → ℝ) (hu : CauchySeq u) :
    ∃ x, Filter.Tendsto u Filter.atTop (nhds x) :=
  cauchySeq_tendsto_of_complete hu
```

```lean +error
#synth CompleteSpace ℚ
```

*Not a class.* Continuity is a structure in `Prop`:

```
structure Continuous [TopologicalSpace X]
    [TopologicalSpace Y] (f : X → Y) : Prop where
  isOpen_preimage : ∀ s, IsOpen s → IsOpen (f ⁻¹' s)
```

A class is for what follows from the type alone. `Continuous f` depends on the function `f`, so it is proved for each `f`, not found by instance search:

```lean
example : Continuous (fun x : ℝ => x) := continuous_id
```

:::table (align := left) +header
* + declaration
  + kind
  + how Lean gets it
* + `TopologicalSpace X`, `MetricSpace X`
  + class with data
  + instance search, from the type
* + `CompleteSpace X`, `CompactSpace X`
  + class in `Prop`
  + instance search, from the type
* + `Continuous f`
  + structure in `Prop`
  + a proof, for each `f`
* + `IsCompact s`
  + `def`
  + a proof, for each `s`
:::

# New type, class, or structure?
%%%
tag := "type-or-class"
%%%

A new mathematical notion can enter Lean in several ways. Which one fits depends on one question: how many such structures are needed on the same type at the same time?

:::table (align := left) +header
* + situation
  + means
  + examples
* + new elements
  + new type (`structure`, `inductive`)
  + `PosNat`, `ℚ`, `ℂ`
* + one canonical structure per type, found by Lean
  + class
  + `Add`, `Group`, `TopologicalSpace`, `MetricSpace`
* + many at once on the same type
  + `structure`; the objects are terms
  + `Filter α`, `Subgroup G`, `Measure α`
* + the same elements with a second structure
  + type synonym with its own instance
  + `Lex α`, `αᵒᵈ`, `WithLp p V`
* + a property of a term
  + `structure` or `def` in `Prop`
  + `Continuous f`, `IsCompact s`
:::

A class means that the type determines the structure. Two instances on the same type lead to {ref "typeclass-diamonds"}[diamonds] or to ambiguity. This is why `Filter` is a structure and not a class: on `ℕ` alone there are `atTop` and `cofinite`, and `Tendsto u atTop (𝓝 x)` uses two filters at once. `Subgroup G` and `Measure α` are structures for the same reason.

```lean
open Filter in
#check (atTop : Filter ℕ)
open Filter in
#check (cofinite : Filter ℕ)
```

`TopologicalSpace` is a class, since a type usually carries one topology. To compare topologies, the class is used as an ordinary type, and its terms are topologies:

```lean
example : (⊥ : TopologicalSpace ℕ) ≤ ⊤ := bot_le
```

A second structure on the same elements as an instance needs a new type with the same elements, as `Lex` in {ref "class-universe"}[chapter 1.6] and `αᵒᵈ` (the reversed order) are. `WithLp p V` gives a product `V` the `ℓᵖ`-norm in place of its own; on `Fin n → ℝ` the norm is the maximum norm, for `EuclideanSpace ℝ (Fin n)` the Euclidean norm ({ref "representation-pitfalls"}[How an object is represented]).

# Managing instances
%%%
tag := "managing-instances"
%%%

A few further knobs control *which* instance is found. You rarely need them at first, but they show up when reading Mathlib:

* *Priorities.* Every instance has a priority, by default `1000`; `instance (priority := 2000) : …` is tried before the others, `instance (priority := 100) : …` after them. Since Lean takes the first solution it finds, priorities resolve overlaps.
* *`local` and `scoped` instances.* A `local instance` is active only until the end of the current section, namespace, or file; a `scoped instance` is active only inside its namespace or once you `open` it. Mathlib uses `scoped` heavily. `open scoped Classical` switches on classical decidability for a whole section; inside a proof the {ref "classical-tactic"}[`classical` tactic] does the same for that proof alone.
* *Default instances.* `@[default_instance]` supplies a fallback when synthesis would otherwise be ambiguous; see {ref "ofnat"}[Where numerals come from] in chapter 1.8.

# Practical tips
%%%
tag := "typeclass-tips"
%%%

* When you get an error like "failed to synthesize instance," it means Lean cannot find a required typeclass instance. Check that your type has the necessary instance defined.
* Use `#check @lemma_name` to see all implicit arguments and understand what instances a lemma requires.
* In Mathlib, most standard types (`ℕ`, `ℤ`, `ℚ`, `ℝ`, `ℂ`) have instances for all the common typeclasses. You rarely need to define instances for these.
* When defining your own types, provide instances for the typeclasses you need. Start with `Repr` (for printing), then `Add`, `Mul`, etc., as needed.
* The `deriving` mechanism can automatically generate instances for some typeclasses (like `Repr` and `DecidableEq`), and copy instances to a type synonym ({ref "deriving-synonym"}[1.6]).
