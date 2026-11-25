import VersoManual
import Manual.Meta
import Leancourse.Markup
import Mathlib

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open MyDef

set_option pp.rawOnError true

#doc (Manual) "Functors, monads, coercions, hierarchies" =>
%%%
htmlSplit := .never
tag := "functors-monads"
%%%

This chapter continues {ref "typeclasses"}[chapter 1.6]. Its classes take a type constructor instead of a type (`Functor`, `Monad`), turn structures into functions (coercions), and build on each other (`extends`).

The [slides](slides/1-7-functors-monads/) for this chapter follow it section by section.

# Classes over type constructors
%%%
tag := "type-constructor-classes"
%%%

The classes so far take a type: `Add ℕ`, `Decidable (2 + 3 = 5)`. A class can also take a *type constructor*, a function `Type → Type` such as `Option` or `List`. The two most important are `Functor` and `Monad`. Both live in `Type 1`, because they quantify over all `α : Type`.

```lean
#check (Functor : (Type → Type) → Type 1)
#check (Monad : (Type → Type) → Type 1)
```

## Functor
%%%
number := false
tag := "functor-typeclass"
%%%

Many type constructors come with a way to apply a function to what they contain. `List.map` applies `g` to every element of a list, `List.map g [a, b] = [g a, g b]`; `Option.map` applies it to the value if there is one, `Option.map g (some a) = some (g a)`. In part 2 the image `f '' s` of a set (chapter 2.2) and `Filter.map` (chapter 2.6) follow the same pattern. A *functor* is a type constructor `f` together with such a map. The class has one field that matters (a second one, `mapConst`, has a default):

```
class Functor (f : Type u → Type v) where
  map : {α β : Type u} → (α → β) → f α → f β
```

`g <$> x` is notation for `Functor.map g x`. For a type constructor of one's own, the instance is written by hand:

```lean
structure Twice (α : Type) where
  fst : α
  snd : α
  deriving Repr

instance : Functor Twice where
  map g p := ⟨g p.fst, g p.snd⟩

#eval (· + 1) <$> (⟨1, 2⟩ : Twice ℕ)
-- { fst := 2, snd := 3 }
```

For `Option` and `List` the instances are in Lean's library, and `<$>` is `Option.map` and `List.map`:

```lean
example (g : ℕ → ℕ) (x : Option ℕ) :
    g <$> x = Option.map g x := rfl
example (g : ℕ → ℕ) (xs : List ℕ) :
    g <$> xs = List.map g xs := rfl
```

`map` applies a function to what is inside, without changing the shape around it:

```lean
#eval (· + 10) <$> (some 5 : Option ℕ)   -- some 15
#eval (· + 10) <$> (none : Option ℕ)     -- none
#eval (· * 2) <$> [1, 2, 3]              -- [2, 4, 6]
```

`map` cannot turn `none` into `some`, and it cannot shorten a list. Two laws say so: mapping the identity changes nothing, and mapping a composition is mapping twice. Here `h ∘ g` is the composition `fun x => h (g x)`. The laws are fields of the class `LawfulFunctor`:

```lean
example (x : Option ℕ) : id <$> x = x := id_map x

example (g h : ℕ → ℕ) (xs : List ℕ) :
    (h ∘ g) <$> xs = h <$> g <$> xs :=
  comp_map g h xs
```

`LawfulFunctor` is a class in `Prop` next to `Functor`. Besides the two laws it has a third field, `map_const`, which says that `mapConst` is `map ∘ Function.const β`. Here `mapConst a x` replaces every entry of `x` by `a` (`mapConst 0 [1, 2, 3] = [0, 0, 0]`), and `Function.const β a` is the constant function `fun _ : β => a`. With the default `mapConst`, `map_const` holds by `rfl`. For `Twice` all three are `rfl`:

```lean
instance : LawfulFunctor Twice where
  map_const := rfl
  id_map _ := rfl
  comp_map _ _ _ := rfl
```

`Functor` itself does not demand the laws. A `map` on lists that also reverses is a valid instance, and it breaks `id_map`. In the example, `local` makes the instance active only until `end`, and `priority := high` makes instance search try it before the library instance ({ref "managing-instances"}[Managing instances] below):

```lean
section
local instance (priority := high) : Functor List where
  map g xs := (xs.map g).reverse
#eval id <$> [1, 2, 3]   -- [3, 2, 1]
end
```

## Monad
%%%
number := false
tag := "monad-typeclass"
%%%

`Option α` is the type of a computation that may fail. Division by zero is the standard case:

```lean
def safeDivide (a b : ℕ) : Option ℕ :=
  if b = 0 then none else some (a / b)
```

To divide twice, the second division must run on the result of the first, and only if there is one. A `Monad m` provides exactly this. The class is built from smaller ones; the two fields without a default are

```
class Monad (m : Type u → Type v)
    extends Applicative m, Bind m
  pure : α → m α
  bind : m α → (α → m β) → m β
```

* `pure : α → m α` turns a value into a computation that returns it;
* `bind : m α → (α → m β) → m β`, written `x >>= f`, runs `x` and passes its result to `f`.

Compared with `Functor`, these two are new. Between the two classes sits `Applicative`, a functor with `pure` and `<*>` (apply a function inside `m` to a value inside `m`); it is not used in this course. `Monad` inherits its fields from six small classes, and all except `pure` and `bind` have a default built from these two:

:::table (align := left) +header
* + Class
  + Field
  + Notation
  + Default in `Monad`
* + `Functor`
  + `map`
  + `<$>`
  + `x >>= pure ∘ g`
* + `Pure`
  + `pure`
  + —
  + none
* + `Seq`
  + `seq`
  + `<*>`
  + from `bind` and `map`
* + `SeqLeft`, `SeqRight`
  + `seqLeft`, `seqRight`
  + `<*`, `*>`
  + from `bind`
* + `Bind`
  + `bind`
  + `>>=`
  + none
:::

`x <* y` runs both `x` and `y` and keeps the result of `x`; `x *> y` keeps the result of `y`. Neither is used here. `Applicative` extends `Functor`, `Pure`, `Seq`, `SeqLeft` and `SeqRight`; `Monad` extends `Applicative` and `Bind`. So every monad is a functor, and an instance of `Monad` only has to give `pure` and `bind`. `#print Monad` lists all fields with their defaults.

For `Option`, `pure` is `some`, and `bind` passes the failure on:

```lean
def optionBind {α β : Type} (x : Option α)
    (f : α → Option β) : Option β :=
  match x with
  | none => none
  | some a => f a

def divideTwice (a b c : ℕ) : Option ℕ :=
  safeDivide a b >>= fun r => safeDivide r c

#eval divideTwice 100 5 4    -- some 5
#eval divideTwice 100 0 4    -- none
```

For `Option` the default `map` agrees with `Option.map`:

```lean
example (g : ℕ → ℕ) (x : Option ℕ) :
    g <$> x = x >>= fun a => pure (g a) := by
  cases x <;> rfl
```

## The `do`-notation
%%%
number := false
tag := "do-notation"
%%%

A chain of `>>=` and `fun` is hard to read. The `do`-notation writes it as a sequence of steps:

```lean
def divideThrice (a b c d : ℕ) : Option ℕ := do
  let r ← safeDivide a b
  let s ← safeDivide r c
  safeDivide s d

#eval divideThrice 1000 10 5 4    -- some 5
#eval divideThrice 1000 10 0 4    -- none
```

`let r ← e` runs `e` and names its result `r`; Lean translates each `let … ←` line into a `>>=`, with the rest of the block as the function. `return a` is `pure a`.

## Lists as a monad
%%%
number := false
tag := "list-monad"
%%%

A list is a computation with several results. `pure a` is `[a]`, and `xs >>= f` applies `f` to each element and concatenates the lists:

```lean
#eval [1, 2] >>= fun x => [x, x * 10]   -- [1, 10, 2, 20]

def pairs : List (ℕ × ℕ) := do
  let x ← [1, 2, 3]
  let y ← [10, 20]
  return (x, y)

#eval pairs
-- [(1, 10), (1, 20), (2, 10), (2, 20), (3, 10), (3, 20)]
```

`let x ← [1, 2, 3]` reads "for each `x` in `[1, 2, 3]`". The result is the list version of `{(x, y) | x ∈ {1, 2, 3}, y ∈ {10, 20}}`. The instance comes from Mathlib (`#synth Monad List` names it).

## The monad laws
%%%
number := false
tag := "monad-laws"
%%%

Three laws make the `do`-notation behave as expected. `pure_bind` and `bind_assoc` are fields of `LawfulMonad`; `bind_pure` is a theorem derived from the other fields:

:::table (align := left) +header
* + law
  + statement
  + Lean
* + left identity
  + `pure a >>= f = f a`
  + `pure_bind`
* + right identity
  + `x >>= pure = x`
  + `bind_pure`
* + associativity
  + `x >>= f >>= g = x >>= fun a => f a >>= g`
  + `bind_assoc`
:::

For `Option` each law is a computation, by cases on `x`:

```lean
example (a : ℕ) (f : ℕ → Option ℕ) :
    (pure a >>= f) = f a := rfl

example (x : Option ℕ) : (x >>= pure) = x := by
  cases x <;> rfl
```

The name comes from category theory. A monad there is a functor `T` with natural transformations `η : Id → T` (here `pure`) and `μ : T ∘ T → T` (here `join`, which is `bind` with the identity: `join x = x >>= id`, in Lean `joinM`), and for the category of types and functions the three laws are equivalent to its axioms.

# Coercions
%%%
tag := "coercions"
%%%

A *coercion* is a conversion Lean inserts automatically when a term of one type appears where another is expected, such as a `ℕ` where a `ℤ` is wanted. Coercions are instances of classes such as `Coe`, so instance resolution drives them too: on a mismatch Lean finds the instance and inserts the conversion, written `↑`.

```lean
example (n : ℕ) : ℤ := n    -- inserted silently
example (n : ℕ) : ℤ := ↑n   -- the same, explicitly
```

There are three flavours, according to *what* the target is:

:::table (align := left) +header
* + Class
  + Converts a term into ...
  + Example
* + `Coe`
  + ... a term of another type
  + a subtype into its base type; `ℕ → ℤ` via `NatCast` (`Nat.cast`, chapter 2.1)
* + `CoeSort`
  + ... a *type* (where a `Sort` is expected)
  + a set as a type; `b : Bool` as the type `b = true`
* + `CoeFun`
  + ... a *function* (in applied position)
  + a bundled morphism `f` applied as `f x`
:::

`Coe` is the ordinary case — one value becomes another:

```lean
-- the subtype's `.val`:
example (s : {n : ℕ // n > 0}) : ℕ := s
```

`CoeSort` lets a term stand in for a *type*. It turns `b : Bool` into the proposition `b = true` where a type is expected, and it is how a `Set α` may be written as a type:

```lean
-- b used as a type:
example (b : Bool) (h : b) : b = true := h
-- the subtype ↥s of its members:
example (s : Set ℕ) : Type := s
```

`CoeFun` lets a *bundled* object be applied like a plain function — so an additive monoid homomorphism `f : ℕ →+ ℕ` can be written `f x` even though `f` is really a structure carrying that function together with its properties:

```lean
example (f : ℕ →+ ℕ) (n : ℕ) : ℕ := f n
```

Mathlib does not write a `CoeFun` instance for each kind of map. Each kind of map registers an instance of the class `DFunLike`, and one generic `CoeFun` instance serves them all ({ref "representation-pitfalls"}[How an object is represented]).

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
* The `deriving` mechanism can automatically generate instances for some typeclasses (like `Repr`, `BEq`, `Hashable`, `Inhabited`).
