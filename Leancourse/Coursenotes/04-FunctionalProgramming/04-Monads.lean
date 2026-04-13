import VersoManual
import Manual.Meta
import Leancourse.Misc.Defs
import Mathlib

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open MyDef

set_option pp.rawOnError true

#doc (Manual) "Monads and Computation Patterns" =>
%%%
htmlSplit := .never
tag := "monads"
%%%

Monads are a design pattern from functional programming that provide a uniform way to sequence computations with additional structure -- such as computations that may fail, that carry state, or that perform input/output. The name "monad" comes from category theory, but in programming they are a practical tool rather than an abstract concept.

# The problem: chaining computations that may fail
%%%
tag := "option-type"
%%%

Consider looking up values in a list of key-value pairs. The lookup might fail if the key is not present. Lean represents this with the `Option` type:

```lean
#check @Option
-- Option : Type u → Type u
```

A value of type `Option α` is either `some a` (for some `a : α`) or `none`. This is like a computation that might produce a result or might fail.

```lean
def safeDivide (a b : ℕ) : Option ℕ :=
  if b == 0 then none else some (a / b)

#eval safeDivide 10 3    -- outputs some 3
#eval safeDivide 10 0    -- outputs none
```

Now suppose we want to chain several such computations: divide `a` by `b`, then divide the result by `c`. Without special support, we would need to write nested pattern matches:

```lean
def chainDivide (a b c : ℕ) : Option ℕ :=
  match safeDivide a b with
  | none => none
  | some r => safeDivide r c

#eval chainDivide 100 5 4    -- outputs some 5
#eval chainDivide 100 0 4    -- outputs none
#eval chainDivide 100 5 0    -- outputs none
```

This nesting becomes deeply unreadable with more steps. Monads solve this problem.

# The `Bind` operation
%%%
tag := "bind-operation"
%%%

The key operation of a monad is `bind` (also written `>>=`). For `Option`, it works like this:

```lean
def myBind (x : Option α) (f : α → Option β) : Option β :=
  match x with
  | none => none
  | some a => f a
```

It says: if `x` is `none`, propagate the failure; if `x` is `some a`, apply `f` to `a`. Now we can rewrite our chained division:

```lean
def chainDivide' (a b c : ℕ) : Option ℕ :=
  safeDivide a b >>= fun r => safeDivide r c
```

This reads naturally: "divide `a` by `b`, then take the result `r` and divide it by `c`."

The monad instance for `Option` is given by:

* `pure (a : α) : Option α := some a`
* `bind (x : Option α) (f : α → Option β) : Option β := match x with | none => none | some a => f a`

So `pure` wraps a value in `some`, and `bind` propagates `none` or applies the continuation `f` to the contained value.

# The `do`-notation
%%%
tag := "do-notation"
%%%

Writing `>>=` and `fun` can still be verbose. Lean provides `do`-notation, which makes monadic code look almost like imperative programming:

```lean
def chainDivideDo (a b c : ℕ) : Option ℕ := do
  let r ← safeDivide a b
  safeDivide r c

#eval chainDivideDo 100 5 4    -- outputs some 5
#eval chainDivideDo 100 0 4    -- outputs none
```

The `let r ← e` syntax means: "run the computation `e`; if it succeeds with value `r`, continue; if it fails, propagate the failure." Under the hood, Lean translates this into `>>=` calls.

We can chain many steps:

```lean
def multiDivide (a b c d : ℕ) : Option ℕ := do
  let r1 ← safeDivide a b
  let r2 ← safeDivide r1 c
  safeDivide r2 d

#eval multiDivide 1000 10 5 4    -- outputs some 5
#eval multiDivide 1000 10 0 4    -- outputs none
```

# The `Functor` typeclass
%%%
tag := "functor-typeclass"
%%%

Before we discuss monads, we need the simpler concept of a *functor*. In Lean, `Functor` is a typeclass for type constructors `f : Type → Type` that support a `map` operation:

* `map : (α → β) → f α → f β` -- applies a function to the value(s) inside the container, without changing the structure.

The infix notation for `map` is `<$>`, so `g <$> x` means `Functor.map g x`. Every monad is automatically a functor (since `map` can be defined in terms of `bind` and `pure`), but the functor interface is useful on its own when you only need to transform values without chaining computations.

Here is what `map` does for each of our examples:

* `Option`: `map f x` applies `f` to the contained value if `x = some a`, giving `some (f a)`, and returns `none` if `x = none`.

```lean
#eval (· + 10) <$> (some 5 : Option ℕ)  -- some 15
#eval (· + 10) <$> (none : Option ℕ)    -- none
```

* `List`: `map f xs` applies `f` to every element of the list, i.e. `List.map f xs`.

```lean
#eval (· * 2) <$> [1, 2, 3]    -- [2, 4, 6]
```

* `IO`: `map f action` produces a new IO action that runs `action` and then applies `f` to its result.

* `StateM σ`: `map f x` runs the stateful computation `x`, obtains result `a` and new state `s'`, and returns `(f a, s')`. The state is threaded through unchanged.

```lean
#eval (Functor.map (· * 10) (get : StateM ℕ ℕ)).run 7
-- outputs (70, 7)
```

* `Except ε`: `map f x` applies `f` to the value if `x = Except.ok a`, giving `Except.ok (f a)`, and returns `Except.error e` unchanged if `x = Except.error e`.

```lean
#eval (· + 1) <$> (Except.ok 5 : Except String ℕ)
-- Except.ok 6
#eval (· + 1) <$> (Except.error "fail" : Except String ℕ)
-- Except.error "fail"
```

* `Set`: `map f s` is the image of `s` under `f`, i.e. `{f a | a ∈ s}`. This is the familiar image operation from mathematics.

* `Filter`: `Filter.map f F` is the pushforward filter. A set `s` belongs to `Filter.map f F` if and only if `f ⁻¹' s ∈ F`. This generalizes the image operation to filters.

* `Finset`: `map f s` applies an embedding `f` to each element of the finite set. For a plain function, one uses `Finset.image f s` instead.

In summary, `map` always means "apply a function inside the container." The key property is that `map` preserves the structure: it cannot change `none` to `some`, shorten a list, or introduce new side effects. It only transforms the values.

# The `Monad` typeclass
%%%
tag := "monad-typeclass"
%%%

In Lean, `Monad` is a typeclass. Any type constructor `m : Type → Type` can be a monad if it provides two operations:

* `pure : α → m α` -- wraps a plain value into the monadic context.
* `bind : m α → (α → m β) → m β` -- chains computations.

These must satisfy the monad laws (associativity and identity), which ensure that `do`-notation behaves sensibly. Every `Monad` is also a `Functor`, with `map f x = x >>= (pure ∘ f)`.

Lean already provides `Monad Option`, `Monad List`, `Monad IO`, and many more. For each monad we encounter below, we will spell out what `pure` and `bind` mean concretely.

# Lists as a monad
%%%
tag := "list-monad"
%%%

Lists can also be viewed as monads, representing computations with multiple possible results:

```lean
def pairs : List (ℕ × ℕ) := do
  let x ← [1, 2, 3]
  let y ← [10, 20]
  return (x, y)

#eval pairs
-- outputs [(1, 10), (1, 20), (2, 10), (2, 20), (3, 10), (3, 20)]
```

Here, `let x ← [1, 2, 3]` means "for each `x` in the list `[1, 2, 3]`," and `return (x, y)` creates a singleton list. The monadic bind for lists is essentially `List.flatMap` (also known as `concatMap` or `List.bind`).

This is similar to set-builder notation in mathematics: `{ (x, y) | x ∈ {1,2,3}, y ∈ {10,20} }`.

The monad instance for `List` is given by:

* `pure (a : α) : List α := [a]`
* `bind (xs : List α) (f : α → List β) : List β := xs.flatMap f`

So `pure` creates a singleton list, and `bind` applies `f` to each element and concatenates the resulting lists. For example, `[1, 2].bind (fun x => [x, x * 10])` evaluates to `[1, 10, 2, 20]`.

# The `IO` monad
%%%
tag := "io-monad"
%%%

Functional programming insists on pure functions, but real programs need to interact with the outside world: reading files, printing to the screen, communicating over a network. The `IO` monad solves this: an `IO α` computation is a description of an action that, when executed, may perform side effects and produce a value of type `α`.

```lean
def greet (name : String) : IO Unit := do
  IO.println s!"Hello, {name}!"
  IO.println "Welcome to Lean."
```

Inside `do`-notation, we can sequence IO actions. The key insight is that `greet` itself is a pure function -- it returns a *description* of actions, not the actions themselves. The actions are only performed when the program runs.

A complete program in Lean is a value of type `IO Unit`:

```lean
def myMain : IO Unit := do
  IO.println "What is 2 + 2?"
  IO.println s!"It is {2 + 2}."
```

The monad instance for `IO` is given by:

* `pure (a : α) : IO α` -- returns `a` without performing any side effect.
* `bind (x : IO α) (f : α → IO β) : IO β` -- first executes the action `x`, obtaining a value `a : α`, then executes `f a`.

Internally, `IO α` is defined as `EStateM IO.Error IO.RealWorld α`, a state monad over a token representing the real world. However, these implementation details are hidden: you cannot pattern-match on an `IO` value.

# Stateful computation with `StateM`
%%%
tag := "state-monad"
%%%

The `StateM` monad allows computations that read and modify state. A value of type `StateM σ α` is a computation that can access and modify state of type `σ` and produces a result of type `α`.

```lean
def counter : StateM ℕ ℕ := do
  let n ← get
  set (n + 1)
  return n

def countThree : StateM ℕ (ℕ × ℕ × ℕ) := do
  let a ← counter
  let b ← counter
  let c ← counter
  return (a, b, c)

#eval countThree.run 0    -- outputs ((0, 1, 2), 3)
```

The `.run` function executes the stateful computation with an initial state. The result `((0, 1, 2), 3)` tells us the three counter values were `0`, `1`, `2`, and the final state is `3`.

The type `StateM σ α` is defined as `σ → (α × σ)`, i.e. a function that takes an initial state and returns a result together with an updated state. The monad instance is:

* `pure (a : α) : StateM σ α := fun s => (a, s)` -- returns `a` and leaves the state unchanged.
* `bind (x : StateM σ α) (f : α → StateM σ β) : StateM σ β := fun s => let (a, s') := x s; f a s'` -- runs `x` with state `s`, obtaining result `a` and new state `s'`, then runs `f a` with state `s'`.

The operations `get : StateM σ σ := fun s => (s, s)` and `set (s' : σ) : StateM σ Unit := fun _ => ((), s')` allow reading and writing the state.

# Error handling with `Except`
%%%
tag := "except-monad"
%%%

The `Except` type is like `Option`, but it carries an error message when something goes wrong:

```lean
def safeDivideE (a b : ℕ) : Except String ℕ :=
  if b == 0 then Except.error "division by zero"
  else Except.ok (a / b)

def computation : Except String ℕ := do
  let r1 ← safeDivideE 100 5
  let r2 ← safeDivideE r1 4
  return r2

#eval computation    -- outputs Except.ok 5

def failingComputation : Except String ℕ := do
  let r1 ← safeDivideE 100 0
  let r2 ← safeDivideE r1 4
  return r2

#eval failingComputation    -- outputs Except.error "division by zero"
```

With `Except ε α`, we can propagate meaningful error messages instead of just `none`.

The type `Except ε α` has two constructors: `Except.ok (a : α)` and `Except.error (e : ε)`. The monad instance is:

* `pure (a : α) : Except ε α := Except.ok a`
* `bind (x : Except ε α) (f : α → Except ε β) : Except ε β := match x with | Except.error e => Except.error e | Except.ok a => f a`

This is exactly analogous to `Option`, but the failure case carries an error value of type `ε` instead of just being `none`.

# Sets as a monad
%%%
tag := "set-monad"
%%%

In mathematics, a natural analogue of the `List` monad is the `Set` monad. A set `s : Set α` represents a nondeterministic choice among the elements of `s`. Mathlib provides a monad instance for `Set`, but it is not registered globally because sets have no computational content (you cannot iterate over an arbitrary `Set`). To use it, we enable it locally:

```lean
section SetMonad
attribute [local instance] Set.monad

def setPairs : Set (ℕ × ℕ) := do
  let x ← ({1, 2, 3} : Set ℕ)
  let y ← ({10, 20} : Set ℕ)
  return (x, y)

example : setPairs = {(1, 10), (1, 20), (2, 10), (2, 20), (3, 10), (3, 20)} := by
  simp [setPairs, Set.bind_def, Set.pure_def]
  ext ⟨a, b⟩
  simp
  omega

end SetMonad
```

The monad instance for `Set` is given by:

* `pure (a : α) : Set α := {a}` -- the singleton set.
* `bind (s : Set α) (f : α → Set β) : Set β := ⋃ a ∈ s, f a` -- the union of all images under `f`.

This is exactly the mathematical counterpart of the `List` monad: where `List.bind` concatenates lists, `Set.bind` takes unions of sets.

# Filters as a monad
%%%
tag := "filter-monad"
%%%

Recall that a filter `F : Filter α` is a collection of sets that is upward closed and closed under finite intersections. Filters generalize the notion of "sets of large elements" or "neighborhoods." Mathlib defines `pure` and `bind` operations for filters:

```lean
#check @Filter.bind
-- Filter.bind : Filter α → (α → Filter β) → Filter β
```

The `Pure` instance for `Filter` is registered so that `pure a` is the principal filter of `{a}`:

* `pure (a : α) : Filter α := 𝓟 {a}` -- the collection of all sets containing `a`. In particular, `s ∈ pure a ↔ a ∈ s`.
* `Filter.bind (F : Filter α) (m : α → Filter β) : Filter β := Filter.join (Filter.map m F)` -- informally, this takes the "union" of the filters `m a` as `a` ranges over `F`.

However, Mathlib does *not* register a `Monad Filter` instance. The reason is that this `bind` is incompatible with the `Applicative Filter` instance (which is based on `Filter.seq`), so the monad laws would not hold with respect to the existing applicative structure. One can still use `pure` and `Filter.bind` directly, but `do`-notation is not available for filters.

# Finite sets and `Finset`
%%%
tag := "finset-monad"
%%%

`Finset α` is the type of finite sets with elements in `α`. Unlike `Set`, finite sets do have computational content, and Mathlib registers a global `Monad Finset` instance.

```lean
section FinsetMonad
open scoped Classical

noncomputable def finsetPairs : Finset (ℕ × ℕ) := do
  let x ← ({1, 2, 3} : Finset ℕ)
  let y ← ({10, 20} : Finset ℕ)
  return (x, y)

end FinsetMonad
```

Note that we need `open scoped Classical` because the `Monad Finset` instance requires all propositions to be decidable. This makes the definition `noncomputable`, so we cannot use `#eval` on it. However, we can still reason about it in proofs.

The monad instance for `Finset` is given by:

* `pure (a : α) : Finset α := {a}` -- the singleton finite set.
* `bind (s : Finset α) (f : α → Finset β) : Finset β := s.sup f` -- which equals `s.biUnion f`, the finite union of all images under `f`.

This is the finite analogue of the `Set` monad.

# Connection to category theory
%%%
tag := "monads-category-theory"
%%%

The name "monad" comes from category theory. In that setting, a monad on a category `C` is an endofunctor `T : C → C` together with natural transformations `η : Id → T` (the unit, corresponding to `pure`) and `μ : T ∘ T → T` (the multiplication, related to `bind`/`join`), satisfying certain coherence conditions.

The programming notion of monad is exactly this, specialized to the category of types and functions. The monad laws in programming:
* `pure a >>= f = f a` -- left identity
* `m >>= pure = m` -- right identity
* `(m >>= f) >>= g = m >>= (fun x => f x >>= g)` -- associativity

correspond precisely to the coherence conditions for monads in category theory. So if you study category theory later, you will find that you already understand monads from a programming perspective.

# Summary
%%%
tag := "monads-summary"
%%%

Monads provide a unified pattern for sequencing computations:

* `Option` -- computations that may fail silently
* `Except ε` -- computations that may fail with an error of type `ε`
* `List` -- computations with multiple results
* `Set` -- nondeterministic choice over (possibly infinite) sets
* `Finset` -- nondeterministic choice over finite sets
* `StateM σ` -- computations with mutable state of type `σ`
* `IO` -- computations with real-world side effects

Filters have `pure` and `bind` operations but do not form a `Monad` instance due to incompatibility with the applicative structure.

The `do`-notation makes monadic code readable and close to imperative style, while preserving the benefits of functional programming (purity, type safety, composability).
