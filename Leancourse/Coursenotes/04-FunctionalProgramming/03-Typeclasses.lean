import VersoManual
import Manual.Meta
import Leancourse.Misc.Defs
import Mathlib

open Verso.Genre Manual
open MyDef

set_option pp.rawOnError true

#doc (Manual) "The Typeclass System" =>
%%%
htmlSplit := .never
tag := "typeclasses"
%%%

Typeclasses are one of the most important features of Lean, and they are central to how Mathlib organizes mathematics. A typeclass is a way to associate operations and properties with types, and to have Lean find the right implementation automatically. If you have seen abstract algebra, typeclasses are the mechanism that lets Lean know that the integers form a ring, that the real numbers form a field, and so on.

# The problem typeclasses solve
%%%
tag := "typeclass-motivation"
%%%

Consider the `+` operator. It works on natural numbers, integers, real numbers, matrices, polynomials, and many other types. How does Lean know which `+` to use?

One approach would be to define different functions: `addNat`, `addInt`, `addReal`, etc. But that would be extremely tedious. Instead, Lean uses typeclasses: there is a single `Add` typeclass, and each type that supports addition provides an `instance` of `Add`.

When you write `a + b`, Lean looks at the types of `a` and `b`, finds the appropriate `Add` instance, and uses it. This process is called *instance resolution* and happens automatically.

# Defining typeclasses
%%%
tag := "defining-typeclasses"
%%%

A typeclass is defined using the `class` keyword. Here is a simplified version of how `Add` might be defined:

```lean
class MyAdd (α : Type) where
  myAdd : α → α → α
```

This says: for any type `α`, an instance of `MyAdd α` provides a function `myAdd : α → α → α`. The `class` keyword is similar to `structure`, but it tells Lean to use the typeclass resolution mechanism.

# Creating instances
%%%
tag := "creating-instances"
%%%

We create instances using the `instance` keyword:

```lean
instance : MyAdd ℕ where
  myAdd := Nat.add

instance : MyAdd ℤ where
  myAdd := Int.add
```

Now we can use `MyAdd.myAdd` on natural numbers and integers, and Lean will automatically find the right instance.

Let us define a custom type and give it an `Add` instance:

```lean
structure Vec2 where
  x : Float
  y : Float

instance : Add Vec2 where
  add a b := { x := a.x + b.x, y := a.y + b.y }

instance : ToString Vec2 where
  toString v := s!"({v.x}, {v.y})"

#eval (⟨1.0, 2.0⟩ : Vec2) + ⟨3.0, 4.0⟩    -- outputs (4.0, 6.0)
```

We defined two instances: `Add Vec2` so we can use `+`, and `ToString Vec2` so Lean can print `Vec2` values.

# The square bracket notation
%%%
tag := "square-bracket-notation"
%%%

When a function needs a typeclass instance, we use square brackets `[...]` in its signature:

```lean
def doubleIt [Add α] (x : α) : α := x + x

#eval doubleIt 5        -- outputs 10
#eval doubleIt (3 : ℤ)  -- outputs 6
```

The `[Add α]` argument tells Lean: "find an `Add` instance for `α` automatically." We do not need to pass it explicitly; Lean's instance resolution handles it.

You can name the instance if you need to refer to it:

```lean
def tripleIt [inst : Add α] (x : α) : α := inst.add x (inst.add x x)
```

But usually the unnamed form `[Add α]` is preferred, since Lean resolves it behind the scenes.

# Inspecting typeclass arguments with `@`
%%%
tag := "inspecting-typeclasses"
%%%

When working with Mathlib, it is often useful to see all the implicit and typeclass arguments of a lemma. The `@` symbol makes all arguments explicit:

```
#check mul_comm
-- mul_comm : ∀ {M : Type u_1} [inst : CommMonoid M] (a b : M), a * b = b * a
```

```
#check @mul_comm
-- @mul_comm : ∀ {M : Type u_1} → CommMonoid M → M → M → M = M
```

The first form shows `[inst : CommMonoid M]` in brackets, meaning it is found automatically. The `@` version shows all arguments explicitly, which helps understand exactly what typeclass constraints are required.

# The algebraic hierarchy in Mathlib
%%%
tag := "algebraic-hierarchy"
%%%

Mathlib uses typeclasses to build an extensive hierarchy of algebraic structures. Here are some key ones, ordered roughly from weakest to strongest:

* `Add α` -- a type with an addition operation
* `Mul α` -- a type with a multiplication operation
* `AddMonoid α` -- a type with addition, an additive identity `0`, and associativity
* `Monoid α` -- a type with multiplication, a multiplicative identity `1`, and associativity
* `Group α` -- a monoid with inverses
* `AddCommGroup α` -- a commutative group under addition
* `Ring α` -- an additive commutative group with a multiplication that distributes over addition
* `CommRing α` -- a ring with commutative multiplication
* `Field α` -- a commutative ring where every nonzero element has an inverse
* `LinearOrder α` -- a type with a total order

Each of these is defined as a `class` that extends simpler classes. For example (simplified):

```
class Group (α : Type) extends Monoid α where
  inv : α → α
  inv_mul_cancel : ∀ a : α, inv a * a = 1
```

When you write a lemma that requires a `CommRing`, Lean automatically knows that it also has `Add`, `Mul`, `AddCommGroup`, etc., because of the `extends` chain.

The power of this system is that we can state and prove theorems at the most general level. For instance, `mul_comm` works for any `CommMonoid`, which includes `ℕ`, `ℤ`, `ℚ`, `ℝ`, `ℂ`, polynomial rings, matrix rings (when the base is commutative), and many more.

# Defining multiple instances
%%%
tag := "multiple-instances"
%%%

Let us build a more complete example. We define a type `Mod3` representing integers modulo 3, and equip it with algebraic structure:

```lean
inductive Mod3 where
  | zero | one | two
  deriving Repr, BEq

instance : Add Mod3 where
  add
    | Mod3.zero, b => b
    | a, Mod3.zero => a
    | Mod3.one, Mod3.one => Mod3.two
    | Mod3.one, Mod3.two => Mod3.zero
    | Mod3.two, Mod3.one => Mod3.zero
    | Mod3.two, Mod3.two => Mod3.one

instance : Mul Mod3 where
  mul
    | Mod3.zero, _ => Mod3.zero
    | _, Mod3.zero => Mod3.zero
    | Mod3.one, b => b
    | a, Mod3.one => a
    | Mod3.two, Mod3.two => Mod3.one

instance : Zero Mod3 where
  zero := Mod3.zero

instance : One Mod3 where
  one := Mod3.one

#eval (Mod3.two + Mod3.two : Mod3)    -- outputs Mod3.one
#eval (Mod3.two * Mod3.two : Mod3)    -- outputs Mod3.one
```

# How instance resolution works
%%%
tag := "instance-resolution"
%%%

When Lean encounters an expression like `a + b` where `a b : α`, it needs to find an instance of `Add α`. The resolution proceeds as follows:

1. Lean looks through all registered instances (those declared with `instance`).
2. It tries to unify the goal `Add α` with the type of each instance.
3. If an instance itself requires other instances (e.g., `Add (Prod α β)` might require `Add α` and `Add β`), Lean recursively resolves those.
4. If exactly one chain of instances leads to a solution, Lean uses it. If none or multiple exist, it reports an error.

This process is deterministic and happens at elaboration time (when Lean checks your code), not at runtime. So there is no performance penalty.

# Practical tips
%%%
tag := "typeclass-tips"
%%%

* When you get an error like "failed to synthesize instance," it means Lean cannot find a required typeclass instance. Check that your type has the necessary instance defined.
* Use `#check @lemma_name` to see all implicit arguments and understand what instances a lemma requires.
* In Mathlib, most standard types (`ℕ`, `ℤ`, `ℚ`, `ℝ`, `ℂ`) have instances for all the common typeclasses. You rarely need to define instances for these.
* When defining your own types, provide instances for the typeclasses you need. Start with `Repr` (for printing), then `Add`, `Mul`, etc., as needed.
* The `deriving` mechanism can automatically generate instances for some typeclasses (like `Repr`, `BEq`, `Hashable`, `Inhabited`).
