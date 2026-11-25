import VersoSlides
import Verso.Doc.Concrete
import Mathlib

open VersoSlides

set_option pp.rawOnError true

/-
Deck for the chapter "Functors, monads, coercions, hierarchies" (part
"Lean and its type theory"): classes over type constructors (`Functor`,
`Monad`, the `do`-notation, the laws), coercions, the algebraic
hierarchy, managing instances. It continues chapter 1.6, deck
`1-6-Typeclasses`.
-/

namespace SlidesFunctorsMonads
#doc (Slides) "Functors, monads, coercions, hierarchies" =>

```css
.reveal section p { font-size: 0.8em; line-height: 1.32; margin: 0.42em 0; }
.reveal section p.key, .reveal section .key p { color: #1b91ff; }
.reveal section table { font-size: 0.62em; margin: 0.2em auto 0.4em; }
.reveal section table th,
.reveal section table td { padding: 0.18em 0.9em; }
.reveal section li { font-size: 0.8em; }
```

# Functors, monads, coercions, hierarchies

Lean and its type theory — chapter 7

# Classes over type constructors

```lean -panel -stretch
#check (Add : Type → Type)
#check (Functor : (Type → Type) → Type 1)
#check (Monad : (Type → Type) → Type 1)
```

- `Add ℕ`: a class over a _type_
- `Functor Option`, `Monad List`: a class over a _type constructor_
- `Type 1`: `Functor` quantifies over all `α : Type`

# Functor

```
class Functor (f : Type u → Type v) where
  map : {α β : Type u} → (α → β) → f α → f β
```

- a type constructor `f` with a way to apply `g : α → β` inside: `f α → f β`
- `g <$> x` is notation for `Functor.map g x`
- examples: `List.map g [a, b] = [g a, g b]`, `Option.map g (some a) = some (g a)`; later `f '' s` (2.2), `Filter.map` (2.6)

# A functor by hand

```lean -panel -stretch
structure Twice (α : Type) where
  fst : α
  snd : α
  deriving Repr

instance : Functor Twice where
  map g p := ⟨g p.fst, g p.snd⟩

#eval (· + 1) <$> (⟨1, 2⟩ : Twice ℕ)
```

One field to fill: `map`. The second field, `mapConst`, has a default.

# `map` on `Option` and `List`

```lean -panel -stretch
#eval (· + 10) <$> (some 5 : Option ℕ)   -- some 15
#eval (· + 10) <$> (none : Option ℕ)     -- none
#eval (· * 2) <$> [1, 2, 3]              -- [2, 4, 6]
```

:::class "key"
`map` changes what is inside, never the shape around it.
:::

# The functor laws

```lean -panel -stretch
example (x : Option ℕ) : id <$> x = x := id_map x

example (g h : ℕ → ℕ) (xs : List ℕ) :
    (h ∘ g) <$> xs = h <$> g <$> xs :=
  comp_map g h xs
```

- mapping the identity changes nothing
- mapping a composition is mapping twice
- `h ∘ g = fun x => h (g x)`

# `LawfulFunctor`

```lean -panel -stretch
instance : LawfulFunctor Twice where
  map_const := rfl
  id_map _ := rfl
  comp_map _ _ _ := rfl
```

- a class in `Prop`, next to `Functor`: the two laws as fields
- third field `map_const`: `mapConst` is `map ∘ Function.const β`; with the default, `rfl`
- `mapConst a x`: every entry replaced by `a` (`mapConst 0 [1,2,3] = [0,0,0]`)
- `Function.const β a = fun _ : β => a`

# `Functor` does not demand the laws

```lean -panel -stretch
section
local instance (priority := high) : Functor List where
  map g xs := (xs.map g).reverse
#eval id <$> [1, 2, 3]
end
```

`local`: only until `end`; `priority := high`: tried before the library instance.

:::class "key"
A valid `Functor` instance that breaks `id_map`. The laws are a separate class.
:::

# Computations that may fail

```lean -panel -stretch
def safeDivide (a b : ℕ) : Option ℕ :=
  if b = 0 then none else some (a / b)

#eval safeDivide 10 2    -- some 5
#eval safeDivide 10 0    -- none
```

- `Option α`: a computation that may fail
- to divide twice, the second division must run on the result of the first, and only if there is one
- a `Monad` provides exactly this

# Monad

```
class Monad (m : Type u → Type v)
    extends Applicative m, Bind m
-- the two fields without a default:
  pure : α → m α
  bind : m α → (α → m β) → m β     -- written x >>= f
```

- `pure a`: the computation that returns `a`
- `x >>= f`: run `x`, pass its result to `f`
- in between sits `Applicative`: `Functor` with `pure` and `<*>` (apply a function inside `m` to a value inside `m`; not used here)
- `map` has a default, `x >>= pure ∘ g`: every monad is a functor

# Where the fields come from

:::table +colHeaders
*
  * class
  * field
  * notation
  * default in `Monad`
*
  * `Functor`
  * `map`
  * `<$>`
  * `x >>= pure ∘ g`
*
  * `Pure`
  * `pure`
  * —
  * none
*
  * `Seq`
  * `seq`
  * `<*>`
  * from `bind` and `map`
*
  * `SeqLeft`, `SeqRight`
  * `seqLeft`, `seqRight`
  * `<*`, `*>`
  * from `bind`
*
  * `Bind`
  * `bind`
  * `>>=`
  * none
:::

`x <* y`, `x *> y`: run both, keep the left/right result; not used here.

`Applicative` extends `Functor`, `Pure`, `Seq`, `SeqLeft`, `SeqRight`; `Monad` extends `Applicative` and `Bind`.

:::class "key"
An instance of `Monad` gives `pure` and `bind`. `#print Monad` shows all fields with their defaults.
:::

# `Option` as a monad

```lean -panel -stretch
def divideTwice (a b c : ℕ) : Option ℕ :=
  safeDivide a b >>= fun r => safeDivide r c

#eval divideTwice 100 5 4    -- some 5
#eval divideTwice 100 0 4    -- none
```

- `pure` is `some`
- `bind` passes `none` on, and otherwise applies the function
- the second division runs only if the first succeeded

# The `do`-notation

```lean -panel -stretch
def divideThrice (a b c d : ℕ) : Option ℕ := do
  let r ← safeDivide a b
  let s ← safeDivide r c
  safeDivide s d

#eval divideThrice 1000 10 5 4    -- some 5
#eval divideThrice 1000 10 0 4    -- none
```

`let r ← e`: run `e`, call the result `r`. Each `let … ←` line is a `>>=`. `return a` is `pure a`.

# Lists as a monad

```lean -panel -stretch
#eval [1, 2] >>= fun x => [x, x * 10]
-- [1, 10, 2, 20]

def pairs : List (ℕ × ℕ) := do
  let x ← [1, 2, 3]
  let y ← [10, 20]
  return (x, y)

#eval pairs
```

`let x ← xs` reads "for each `x` in `xs`".

# The monad laws

:::table +colHeaders
*
  * law
  * statement
  * Lean
*
  * left identity
  * `pure a >>= f = f a`
  * `pure_bind`
*
  * right identity
  * `x >>= pure = x`
  * `bind_pure`
*
  * associativity
  * `x >>= f >>= g = x >>= fun a => f a >>= g`
  * `bind_assoc`
:::

```lean -panel -stretch
example (x : Option ℕ) : (x >>= pure) = x := by
  cases x <;> rfl
```

:::class "key"
Category theory: a functor with `η = pure : α → m α` and `μ = join : m (m α) → m α`, `join x = x >>= id` (Lean: `joinM`).
:::

# Coercions

A coercion: a conversion Lean inserts when a term of type `α` stands where `β` is expected, written `↑`. Coercions are instances.

:::table +colHeaders
*
  * Class
  * Converts a term into ...
  * Example
*
  * `Coe`
  * a term of another type
  * subtype into base type; `ℕ → ℤ` via `NatCast` (`Nat.cast`, chapter 2.1)
*
  * `CoeSort`
  * a type
  * a set as a type; `b : Bool` as the type `b = true`
*
  * `CoeFun`
  * a function
  * a bundled morphism applied as `f x`
:::

```lean -panel -stretch
example (n : ℕ) : ℤ := n     -- written ↑n
example (b : Bool) (h : b) : b = true := h  -- b as a type
example (s : Set ℕ) : Type := s
example (f : ℕ →+ ℕ) (n : ℕ) : ℕ := f n
```

# Bundled maps

- `f : ℕ →+ ℕ` is a structure: a function and the proofs that it preserves `0` and `+`
- `f n` works through the class `DFunLike`

:::class "key"
Each kind of map registers `DFunLike`; one generic `CoeFun` instance serves them all.
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

# Managing instances

- `instance (priority := 2000)`: tried before the default `1000`
- Lean takes the first solution it finds
- `local instance`: until the end of the section
- `scoped instance`: inside its namespace, or after `open`
- `@[default_instance]`: a bare `2` defaults to `ℕ`
- "failed to synthesize": an instance is missing

# Summary

- `Functor` and `Monad` are classes over type constructors
- `map`, `pure`, `bind`; the `do`-notation is a chain of `>>=`
- `Option`: computations that may fail; `List`: several results
- coercions are instances of `Coe`, `CoeSort`, `CoeFun`
- the algebraic hierarchy is a chain of `extends`
