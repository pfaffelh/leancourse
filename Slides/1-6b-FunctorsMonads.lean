import VersoSlides
import Verso.Doc.Concrete
import Mathlib

open VersoSlides

set_option pp.rawOnError true

/-
Deck for the second lecture on the chapter "Typeclasses" (part "Lean
and its type theory"): classes over type constructors (`Functor`,
`Monad`, the `do`-notation, the laws), coercions, the algebraic
hierarchy, managing instances. The first lecture is `1-6-Typeclasses`.
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

Lean and its type theory — chapter 6, second lecture

# Classes over type constructors

```lean -panel -stretch
#check (Add : Type → Type)
#check (Functor : (Type → Type) → Type 1)
#check (Monad : (Type → Type) → Type 1)
```

- `Add ℕ`: a class over a _type_
- `Functor Option`, `Monad List`: a class over a _type constructor_

# Functor

`map : (α → β) → f α → f β`, written `g <$> x`

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
- both are fields of `LawfulFunctor`

# Monad

```lean -panel -stretch
def safeDivide (a b : ℕ) : Option ℕ :=
  if b = 0 then none else some (a / b)

def divideTwice (a b c : ℕ) : Option ℕ :=
  safeDivide a b >>= fun r => safeDivide r c

#eval divideTwice 100 5 4    -- some 5
#eval divideTwice 100 0 4    -- none
```

- `pure : α → m α`
- `bind : m α → (α → m β) → m β`, written `x >>= f`
- for `Option`: `pure` is `some`, `bind` passes `none` on

# The `do`-notation

```lean -panel -stretch
def divideThrice (a b c d : ℕ) : Option ℕ := do
  let r ← safeDivide a b
  let s ← safeDivide r c
  safeDivide s d

#eval divideThrice 1000 10 5 4    -- some 5
#eval divideThrice 1000 10 0 4    -- none
```

`let r ← e`: run `e`, call the result `r`. Each line is a `>>=`.

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
In category theory: a functor with `η = pure` and `μ = join`.
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

# Bundled maps

- `f : ℕ →+ ℕ` is a structure: a function and the proofs that it preserves `0` and `+`
- `f n` works through the class `DFunLike`
- a type of maps registers `DFunLike` once; the coercion to functions follows

:::class "key"
One instance per kind of map, not one per map.
:::

# The algebraic hierarchy

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

- `extends` makes `Monoid α` a field; `Group.toMonoid` is an instance
- `mul_comm` is stated once, for `CommMonoid`
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
