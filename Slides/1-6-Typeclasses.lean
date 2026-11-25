import VersoSlides
import Verso.Doc.Concrete
import Mathlib

open VersoSlides

set_option pp.rawOnError true

/-
Deck for the chapter "Typeclasses" (part "Lean and its type theory"),
up to `Decidable` and the `classical` tactic. The next chapter, with
its own deck `1-7-FunctorsMonads`, continues with functors, monads,
coercions and hierarchies. Small sections are merged (square brackets
with `@`).
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

Lean and its type theory — chapter 6

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
- `class` for _canonical_ structure on a type: `AddGroup` on `ℤ`

# Data classes and Prop classes

```lean -panel -stretch
#check (Add ℕ)        -- Type
#check @Nonempty      -- Sort u → Prop
example (h₁ h₂ : Nonempty ℕ) : h₁ = h₂ := rfl
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

`instance foo : C := …` is roughly `@[instance] def foo : C := …`; the attribute `@[instance]` marks the `def` for instance search.

The kernel knows neither `class` nor `instance`: the elaborator writes the instance into the term.

The instance fixes the meaning: `(1, 5) ≤ (2, 0)` is false on `ℕ × ℕ`, true on `Lex (ℕ × ℕ)`.

:::class "key"
Typeclasses add nothing to the logic.
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

`s!"…{e}…"`: a string with the value of `e` inserted.

# Using `deriving`

```lean -panel -stretch
structure Student where
  name : String
  age : ℕ
  deriving Repr, BEq

def alice : Student := { name := "Alice", age := 22 }
#eval alice
#eval alice == alice
```

Without `deriving BEq`: `failed to synthesize BEq Student`. A _deriving handler_ reads the constructors and writes the `instance`; the kernel checks it.

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
def doubleIt {α : Type} [Add α] (x : α) : α :=
  x + x

#eval doubleIt 5        -- 10
#eval doubleIt (3 : ℤ)  -- 6
```

- `(...)` you supply, `{...}` by unification, `[...]` by instance search
- `@mul_comm ℕ _ 2 3`: all arguments explicit, `_` for the instance `CommMagma ℕ`

# Defining multiple instances

```lean -panel -stretch
inductive Mod3 where
  | zero | one | two
  deriving Repr, BEq
instance : Add Mod3 where
  add
    | .zero, b => b
    | a, .zero => a
    | .one, .one => .two
    | .two, .two => .one
    | _, _ => .zero
#eval Mod3.two + Mod3.two
```

`Mul`, `Zero` and `One` in the same way, one `instance` each.

# How instance resolution works

1. look through all registered instances
2. unify the goal `Add α` with each instance's type
3. resolve required instances recursively
4. the first chain found is used; none: error

```lean -panel -stretch
#check (inferInstance : AddCommMonoid ℕ)
```

`inferInstance`: the instance Lean finds; here: does `ℕ` have an `AddCommMonoid` (commutative `+` with `0`)?

:::class "key"
This happens at elaboration time, not at runtime.
:::

# Output parameters

```
-- simplified:
HMul : Type u₁ → Type u₂ → outParam (Type u₃) → Type _
```

- `a * b` is `HMul.hMul a b` with `a : α`, `b : β`, result `γ`
- normally all arguments of a class are search keys; an `outParam` is _read off_ the instance found
- `HMul α β _` is found from `α`, `β`; `γ` is read off
- `x ^ n` with `x : ℝ`, `n : ℕ`: `HPow ℝ ℕ ℝ`
- same for `a ∈ s`: `Membership` has the element type as `outParam`

# Propositions as instances

```lean -panel -stretch
example (p : ℕ) (hp : p.Prime) (a : ZMod p)
    (ha : a ≠ 0) : a * a⁻¹ = 1 := by
  have : Fact p.Prime := ⟨hp⟩
  exact mul_inv_cancel₀ ha
```

- `hp : p.Prime` is invisible to instance search: `Nat.Prime` is not a class
- `Fact p`: a class with one field `out : p`
- `mul_inv_cancel₀ : a ≠ 0 → a * a⁻¹ = 1`, needs a field; `Field (ZMod p)` needs `[Fact (Nat.Prime p)]`

# Using `Fact`

```lean -panel -stretch
example (p : ℕ) [Fact p.Prime] : 2 ≤ p :=
  (Fact.out : p.Prime).two_le

instance : Fact (Nat.Prime 7) := ⟨by norm_num⟩
```

- require: `[Fact p.Prime]`; read back: `Fact.out`
- provide: an `instance` for a concrete value, or `have` in a proof

:::class "key"
Instance search does not reason: each `Fact` is supplied as asked.
:::

# The `Decidable` typeclass

```lean -panel -stretch
#check @Decidable  -- Prop → Type
#eval (inferInstance : Decidable (2 + 3 = 5))
example : 2 + 3 = 5 := by decide
example : ¬(2 + 3 = 6) := by decide
```

- from chapter 1.5: constructors `isTrue h` and `isFalse h`
- `if P then _ else _` needs `Decidable P`
- `decide` evaluates the instance and succeeds if it reduces to `isTrue`; on `ℝ` it gets stuck at `Classical.choice`

# A `Decidable` instance by hand

```lean -panel -stretch
def decZero (n : Nat) : Decidable (n = 0) :=
  match n with
  | 0     => isTrue rfl
  -- a proof that m + 1 ≠ 0
  | m + 1 => isFalse (Nat.succ_ne_zero m)
```

Each branch carries a proof, so `Decidable` lives in `Type`.
`deriving DecidableEq` generates such a definition.

:::class "key"
Registered as an `instance`, `decZero` is what `decide` runs.
:::

# `Decidable`: a family, not a proposition

- `isTrue h : Decidable P` for any proof `h`: says nothing
- `DecidableEq α`: one algorithm for all `a = b`
- `x = 0` on `ℝ`: no algorithm; Mathlib's `DecidableEq ℝ` is by choice
- `if x = 0 then …` on `ℝ`: must be `noncomputable`

:::class "key"
An algorithm needs no axiom, and its code runs. Without one, the instance comes from choice.
:::

# The `classical` tactic

```lean -panel -stretch
example (P : Prop) : ∃ b : Bool, (b = true ↔ P) := by
  classical
  exact ⟨decide P, decide_eq_true_iff⟩
```

- `decide P` needs `Decidable P`; without `classical`: failed to synthesize

- `Classical.propDecidable P : Decidable P` for every `P`, by choice, `noncomputable`
- `classical`: a local instance for the rest of the proof, low priority
- needed in the _statement_: `[DecidableEq β]` as a hypothesis
- `by_cases` needs none of this

# Summary

- a class is a structure, an instance is a term, both marked for search
- data classes live in `Type`, Prop classes in `Prop`
- `[C α]` arguments are filled by instance resolution at elaboration time
- `Decidable` runs through instances
- `Fact` makes a proposition an instance argument
- `classical` makes every proposition decidable inside a proof
