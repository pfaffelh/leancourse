import VersoManual
import Manual.Meta
import Leancourse.Misc.Defs
import Mathlib

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open MyDef

set_option pp.rawOnError true

#doc (Manual) "Typeclasses" =>
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

This says: for any type `α`, an instance of `MyAdd α` provides a function `myAdd : α → α → α`. The `class` keyword is *almost* the same as `structure` -- in fact, every `class` is internally a `structure`. The difference is operational:

- A `structure` is constructed and passed *explicitly*: you write `⟨...⟩` or call its named projections.
- A `class` is also a structure, but Lean's *instance resolution* will synthesize one for you whenever a function expects an `[Add α]` argument. You never write the instance argument by hand.

So the rule of thumb is: use `structure` when the value is part of the data the user manipulates (a `Point`, a `Person`, a `RingHom`); use `class` when the value is a *canonical* piece of structure attached to a type (a `Group` instance on `ℤ`, an `Add` instance on `ℕ`) and you want Lean to find it automatically.

# Data classes and Prop classes
%%%
tag := "class-universe"
%%%

Because a `class` is a `structure`, the applied class `C α` is an ordinary *type*, and an *instance* is simply a *term* of that type. Its universe follows the same rule as any {ref "structures"}[structure] -- the largest universe among its fields -- and this splits typeclasses into two kinds.

*Data classes* bundle operations, so they carry `Type`-valued fields and live in `Type`. Their instances are *data*: a record of operations and proofs, carried at runtime and projected like any structure.

```lean
#check (Monoid ℕ)                    -- Type
#check (inferInstance : Monoid ℕ)    -- a term of it -- data
```

*Prop classes* have only propositional fields, so they live in `Prop`, and their instances are *proofs*. Mathlib's `Fact` is the standard example -- it merely packages a proof of `p` as a searchable instance.

```lean
#check @Fact                          -- Prop → Prop
```

Being a proposition, a `Prop` class inherits {ref "types"}[proof irrelevance]: any two instances are definitionally equal. That is a feature -- such an instance can never *conflict* with another, and it is erased at runtime.

```lean
example (h₁ h₂ : Fact (2 = 2)) : h₁ = h₂ := rfl
```

So typeclasses simply inherit the *proof* / *data* split we drew for terms in general: an instance is data or a proof exactly according to whether its class lives in `Type` or `Prop`.

It is worth being precise about the *role* such a term plays. You genuinely *do* construct it -- that is exactly what `instance … where …` does, and its fields are ordinary values you can project and run. But you then use it as a *property of the type*: declared once, synthesized automatically wherever `[C α]` is required, and essentially never named or passed by hand. For a data class it stays genuine data (carried at runtime); for a `Prop` class it degenerates to *just the fact that it holds* -- a proof, erased. So "an instance is only a property, not a term" is right about the *usage* but not the *substance*: the term is really there; you simply delegate its construction and handling to instance resolution.

The parallel is exact at the term level, too. Just as `class` is a `structure` marked for instance search, `instance` is a `def` marked for instance search: `instance foo : C := …` is sugar for `@[instance] def foo : C := …`. (A plain `def` of a class type is a perfectly good term -- only invisible to the search.)

:::table (align := left) +header
* + Level
  + plain
  + registered for search
* + type (constructor)
  + `structure`
  + `class`
* + term (value)
  + `def`
  + `instance`
:::

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

# Using `deriving`
%%%
tag := "deriving"
%%%

Writing instances by hand is not always necessary: for a range of
standard typeclasses Lean can generate the instance automatically, if
you append a `deriving` clause to the type definition.

```lean
structure Student where
  name : String
  age : ℕ
  deriving Repr

def alice : Student := { name := "Alice", age := 22 }
#eval alice    -- outputs { name := "Alice", age := 22 }
```

Without `deriving Repr`, the `#eval` command would not know how to print a `Student`. The `deriving` clause tells Lean to automatically create a `Repr` instance. Here is what the commonly derived classes provide:

:::table +header
* + Typeclass
  + What it provides
* + `Repr`
  + a way to *display* a value (needed by `#eval`)
* + `BEq`
  + Boolean equality `a == b`
* + `Hashable`
  + a hash function (for use in hash maps/sets)
* + `Inhabited`
  + a designated *default* value `default : α`
* + `DecidableEq`
  + a *decidable* equality test `a = b` (returns a proof either way)
:::

Several instances can be derived at once:

```lean
structure Pair (α β : Type) where
  fst : α
  snd : β
  deriving Repr, BEq, Hashable
```

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

So `[...]` is the *typeclass bracket*: it marks an instance argument, filled by instance search -- as opposed to `(...)`, which you supply yourself, and `{...}`, which Lean infers by unification. The four kinds of binder brackets `()`, `{}`, `⦃⦄`, and `[]` are contrasted side by side in {ref "parenthesis"}[the appendix on parentheses].

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

You can trigger instance resolution yourself with the term
`inferInstance`, which asks Lean to synthesize an instance of a stated
type -- a handy way to ask "does this type have that structure?":

```lean
-- "Does ℕ have an AddCommMonoid instance?" -- yes.
#check (inferInstance : AddCommMonoid ℕ)
```

If no such instance exists, the command fails with a readable error
message. This is exactly the mechanism the `[...]` arguments rely on
behind the scenes.

# Output parameters
%%%
tag := "outparam"
%%%

By default, instance search treats *all* of a class's arguments as search keys: it must know them to look up an instance. Occasionally one argument is *determined by* the instance rather than given in advance. Marking it `outParam` tells Lean: do not wait for this argument -- find the instance from the others, and *read this one off* the result.

The standard example is heterogeneous multiplication `a * b`, whose result type need not match the arguments:

```lean
#check @HMul
-- HMul : Type → Type → outParam Type → Type
```

Because the result `γ` is an `outParam`, Lean resolves `HMul α β ?γ` from `α` and `β` alone and *learns* `γ` from the chosen instance. The same device lets `a ∈ s` infer the element type from the collection -- `Membership`'s element type is an `outParam` too. This is why you often see it in Mathlib signatures, and why the `CoeSort … → outParam Sort` from the previous section is written that way.

# The `Decidable` typeclass
%%%
tag := "decidable-typeclass"
%%%

One typeclass deserves special mention, because it sits at the border
between *programs* and *proofs*: `Decidable`. A proposition `P` is
`Decidable` when there is an algorithm that determines whether `P`
holds -- so the class carries genuine computational content, and lives
in `Type`, not `Prop`:

```lean
#check @Decidable
-- Decidable : Prop → Type

-- Many concrete propositions are decidable, and the
-- instance is found by typeclass resolution:
#check (inferInstance : Decidable (2 + 3 = 5))  -- isTrue ..
#check (inferInstance : Decidable (2 + 3 = 6))  -- isFalse ..
```

Two everyday features rest on this instance search:

* An `if P then _ else _` requires a `Decidable P` instance -- that is
  how the program knows which branch to take. This is also why
  {ref "deriving"}[`deriving DecidableEq`] (above) is useful: it makes
  `a = b` decidable, so you may branch on equality of your own type.
* The `decide` tactic closes any goal whose proposition is decidable,
  simply by running that algorithm and checking the answer is
  `isTrue`:

```lean
example : 2 + 3 = 5 := by decide
example : ¬(2 + 3 = 6) := by decide
```

Decidability is the *constructive* half of the story: it works without
any axioms, which is exactly why the resulting code is executable. The
*classical* counterpart -- making *every* proposition decidable
non-constructively, at the cost of executability -- belongs to the
axioms of Lean and is discussed in the {ref "constructive-classical"}[Mathematics part].

# Coercions
%%%
tag := "coercions"
%%%

A *coercion* is a conversion that Lean inserts *automatically* when a term of one type appears where another is expected -- for instance a `ℕ` used where a `ℤ` is wanted. Like everything in this chapter, it is driven by *instance resolution*: coercions are registered as instances of the class `Coe`, and when a mismatch could be bridged by one, Lean finds it and inserts the conversion, written `↑`.

```lean
example (n : ℕ) : ℤ := n      -- inserted silently
example (n : ℕ) : ℤ := ↑n     -- the same, written explicitly
```

There are three flavours, according to *what* the target is:

:::table (align := left) +header
* + Class
  + Converts a term into ...
  + Example
* + `Coe`
  + ... a term of another type
  + `ℕ → ℤ`; a subtype into its base type
* + `CoeSort`
  + ... a *type* (where a `Sort` is expected)
  + a set as a type; `Bool → Prop`
* + `CoeFun`
  + ... a *function* (in applied position)
  + a bundled morphism `f` applied as `f x`
:::

`Coe` is the ordinary case -- one value becomes another:

```lean
example (s : {n : ℕ // n > 0}) : ℕ := s   -- the subtype's `.val`
```

`CoeSort` lets a term stand in for a *type*. This is exactly the `Bool → Prop` bridge from the {ref "decidable-typeclass"}[previous section] (`b` becomes `b = true`), and it is how a `Set α` may be written where a type is expected:

```lean
example (b : Bool) : Prop := b
example (s : Set ℕ) : Type := s   -- the subtype ↥s of its members
```

`CoeFun` lets a *bundled* object be applied like a plain function -- so an algebra homomorphism can be written `f x` even though `f` is really a structure carrying that function together with its properties:

```lean
example (f : ℕ →+ ℕ) (n : ℕ) : ℕ := f n
```

Coercions keep statements readable: you write `n + r` for `n : ℕ` and `r : ℝ`, and Lean silently reads it as `↑n + r`. The flip side is that a goal can quietly fill with `↑`s that block tactics like `ring` or `linarith`; the {ref "coercion-headaches"}[appendix] covers the numeric chain `ℕ → ℤ → ℚ → ℝ` and the `norm_cast` / `push_cast` tactics that tidy them up.

# Where numerals come from (`OfNat`)
%%%
tag := "ofnat"
%%%

Even a plain numeral is resolved through a typeclass. Writing `2` is sugar for `OfNat.ofNat 2`:

```lean
#check @OfNat.ofNat
-- {α : Type} → (n : ℕ) → [OfNat α n] → α
```

So `(2 : α)` means "the element of `α` denoted by the numeral `2`", available for any `α` that has an `OfNat α 2` instance. That is why the same `2` works across types,

```lean
#check (2 : ℤ)
#check (2 : ℝ)
```

and why you can give a numeral to your own type simply by providing the instance:

```lean
structure Countdown where
  val : Nat

instance (n : Nat) : OfNat Countdown n where
  ofNat := ⟨n⟩

#eval (5 : Countdown).val    -- 5
```

# Managing instances
%%%
tag := "managing-instances"
%%%

A few further knobs control *which* instance is found. You rarely need them at first, but they show up when reading Mathlib:

* *Priorities.* `instance (priority := 1000) : …` makes an instance tried earlier (the default priority is `1000`). Since Lean takes the first solution it finds, priorities resolve overlaps.
* *`local` and `scoped` instances.* A `local instance` is active only until the end of the current section, namespace, or file; a `scoped instance` is active only inside its namespace or once you `open` it. Mathlib uses `scoped` heavily -- `open scoped Classical`, for instance, switches on classical decidability exactly where you want it.
* *Default instances.* `@[default_instance]` supplies a fallback when synthesis would otherwise be ambiguous -- it is how a bare numeral like `2` defaults to `ℕ` when nothing else pins down its type.

# Practical tips
%%%
tag := "typeclass-tips"
%%%

* When you get an error like "failed to synthesize instance," it means Lean cannot find a required typeclass instance. Check that your type has the necessary instance defined.
* Use `#check @lemma_name` to see all implicit arguments and understand what instances a lemma requires.
* In Mathlib, most standard types (`ℕ`, `ℤ`, `ℚ`, `ℝ`, `ℂ`) have instances for all the common typeclasses. You rarely need to define instances for these.
* When defining your own types, provide instances for the typeclasses you need. Start with `Repr` (for printing), then `Add`, `Mul`, etc., as needed.
* The `deriving` mechanism can automatically generate instances for some typeclasses (like `Repr`, `BEq`, `Hashable`, `Inhabited`).
