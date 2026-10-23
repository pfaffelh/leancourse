import VersoSlides
import Verso.Doc.Concrete
import Mathlib

open VersoSlides

set_option pp.rawOnError true

/-
Deck for the chapter "Typeclasses" (part "Lean and its type theory").
It follows the chapter section by section; small sections are merged
(square brackets with `@`, managing instances with the practical tips).
-/

namespace SlidesTypeclasses
#doc (Slides) "Typeclasses" =>

```css
.reveal section p { font-size: 0.8em; line-height: 1.32; margin: 0.42em 0; }
.reveal section p.key, .reveal section .key p { color: #1b91ff; }
.reveal section table { font-size: 0.62em; margin: 0.2em auto 0.4em; }
.reveal section table th,
.reveal section table td { padding: 0.18em 0.9em; }
.reveal section li { font-size: 0.8em; }
```

# Typeclasses

Lean and its type theory — chapter 4

# The problem typeclasses solve

`+` works on `ℕ`, `ℤ`, `ℝ`, matrices, polynomials, ...

- not `addNat`, `addInt`, `addReal`, ...
- one class `Add`, one `instance` per type
- `a + b`: Lean finds the `Add` instance from the types

:::class "key"
This is _instance resolution_. It happens automatically.
:::

# Defining typeclasses

```lean -panel -stretch
class MyAdd (α : Type) where
  myAdd : α → α → α

instance : MyAdd ℕ where
  myAdd := Nat.add
```

- every `class` is internally a `structure`
- a `structure` is passed explicitly, a `class` is synthesized
- `class` for _canonical_ structure on a type: `Group` on `ℤ`

# Data classes and Prop classes

```lean -panel -stretch
#check (Monoid ℕ)     -- Type
#check @Fact          -- Prop → Prop
example (h₁ h₂ : Fact (2 = 2)) : h₁ = h₂ := rfl
```

- _data classes_ live in `Type`; instances are data
- _Prop classes_ live in `Prop`; instances are proofs

:::class "key"
Two instances of a Prop class are definitionally equal: they never conflict.
:::

# Instances are terms

:::table +colHeaders
*
  * Level
  * plain
  * registered for search
*
  * type (constructor)
  * `structure`
  * `class`
*
  * term (value)
  * `def`
  * `instance`
:::

`instance foo : C := …` is sugar for `@[instance] def foo : C := …`.

:::class "key"
The term is there; its construction is delegated to instance resolution.
:::

# Creating instances

```lean -panel -stretch
structure Vec2 where
  x : Float
  y : Float
instance : Add Vec2 where
  add a b := { x := a.x + b.x, y := a.y + b.y }
instance : ToString Vec2 where
  toString v := s!"({v.x}, {v.y})"
#eval (⟨1.0, 2.0⟩ : Vec2) + ⟨3.0, 4.0⟩
```

`Add Vec2` gives `+`, `ToString Vec2` lets Lean print values.

# Using `deriving`

```lean -panel -stretch
structure Student where
  name : String
  age : ℕ
  deriving Repr

def alice : Student := { name := "Alice", age := 22 }
#eval alice
```

Without `deriving Repr`, `#eval` cannot print a `Student`.

# Commonly derived classes

:::table +colHeaders
*
  * Typeclass
  * What it provides
*
  * `Repr`
  * a way to display a value (needed by `#eval`)
*
  * `BEq`
  * Boolean equality `a == b`
*
  * `Hashable`
  * a hash function
*
  * `Inhabited`
  * a default value `default : α`
*
  * `DecidableEq`
  * a decidable equality test `a = b`
:::

Several at once: `deriving Repr, BEq, Hashable`.

# The square bracket notation

```lean -panel -stretch
def doubleIt [Add α] (x : α) : α := x + x

#eval doubleIt 5        -- 10
#eval doubleIt (3 : ℤ)  -- 6
```

- `(...)` you supply, `{...}` by unification, `[...]` by instance search
- `#check @mul_comm` makes every argument explicit,
  including the instance `CommMonoid M`

# The algebraic hierarchy in Mathlib

- `Add`, `Mul`, `AddMonoid`, `Monoid`
- `Group`, `AddCommGroup`, `Ring`, `CommRing`, `Field`
- `LinearOrder`

```
class Group (α : Type) extends Monoid α where
  inv : α → α
  inv_mul_cancel : ∀ a : α, inv a * a = 1
```

:::class "key"
`mul_comm` holds for every `CommMonoid`: `ℕ`, `ℤ`, `ℚ`, `ℝ`, `ℂ`, polynomial rings, ...
:::

# Defining multiple instances

```lean -panel -stretch
inductive Mod3 where
  | zero | one | two
  deriving Repr, BEq
instance : Zero Mod3 where
  zero := Mod3.zero
instance : One Mod3 where
  one := Mod3.one
```

`Add` and `Mul` by pattern matching on the three constructors;
then `Mod3.two + Mod3.two` evaluates to `Mod3.one`.

# How instance resolution works

1. look through all registered instances
2. unify the goal `Add α` with each instance's type
3. resolve required instances recursively
4. exactly one chain: use it; none or several: error

```lean -panel -stretch
#check (inferInstance : AddCommMonoid ℕ)
```

:::class "key"
This happens at elaboration time, not at runtime.
:::

# Output parameters

```lean -panel -stretch
#check @HMul
-- Type → Type → outParam Type → Type
```

- normally all arguments of a class are search keys
- an `outParam` is _read off_ the instance found
- `HMul α β ?γ` is resolved from `α` and `β`; `γ` is learned
- same for `a ∈ s`: `Membership` has the element type as `outParam`

# The `Decidable` typeclass

```lean -panel -stretch
#check @Decidable  -- Prop → Type
#check (inferInstance : Decidable (2 + 3 = 5))
example : 2 + 3 = 5 := by decide
example : ¬(2 + 3 = 6) := by decide
```

- `if P then _ else _` needs `Decidable P`
- `decide` runs the algorithm and checks for `isTrue`

# A `Decidable` instance by hand

```lean -panel -stretch
def decZero (n : Nat) : Decidable (n = 0) :=
  match n with
  | 0     => isTrue rfl
  | m + 1 => isFalse (Nat.succ_ne_zero m)
```

Each branch carries a proof, so `Decidable` lives in `Type`.
`deriving DecidableEq` generates such a definition.

:::class "key"
Decidability is the constructive half; the code is executable.
:::

# Coercions

:::table +colHeaders
*
  * Class
  * Converts a term into ...
  * Example
*
  * `Coe`
  * a term of another type
  * `ℕ → ℤ`; subtype into base type
*
  * `CoeSort`
  * a type
  * a set as a type; `Bool → Prop`
*
  * `CoeFun`
  * a function
  * a bundled morphism applied as `f x`
:::

```lean -panel -stretch
example (n : ℕ) : ℤ := n     -- written ↑n
example (b : Bool) : Prop := b
example (s : Set ℕ) : Type := s
example (f : ℕ →+ ℕ) (n : ℕ) : ℕ := f n
```

# Where numerals come from

`2` is sugar for `OfNat.ofNat 2`; it works for every `α` with an `OfNat α 2` instance.

```lean -panel -stretch
structure Countdown where
  val : Nat

instance (n : Nat) : OfNat Countdown n where
  ofNat := ⟨n⟩

#eval (5 : Countdown).val    -- 5
```

# Managing instances, practical tips

- `instance (priority := 1000)`: overlaps are resolved by order
- `local instance`, `scoped instance`: e.g. `open scoped Classical`
- `@[default_instance]`: a bare `2` defaults to `ℕ`
- "failed to synthesize instance": an instance is missing
- own types: start with `Repr`, then `Add`, `Mul`, ...

# Summary

- a class is a structure, an instance is a term, both marked for search
- data classes live in `Type`, Prop classes in `Prop`
- `[C α]` arguments are filled by instance resolution at elaboration time
- Mathlib's algebraic hierarchy is a chain of `extends`
- `Decidable`, coercions and numerals all run through instances
