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

# The `Monad` typeclass
%%%
tag := "monad-typeclass"
%%%

In Lean, `Monad` is a typeclass. Any type constructor `m : Type → Type` can be a monad if it provides two operations:

* `pure : α → m α` -- wraps a plain value into the monadic context.
* `bind : m α → (α → m β) → m β` -- chains computations.

These must satisfy the monad laws (associativity and identity), which ensure that `do`-notation behaves sensibly.

For `Option`:
* `pure a` is `some a`
* `bind` is the pattern-matching function we saw above

Lean already provides `Monad Option`, `Monad List`, `Monad IO`, and many more.

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
* `StateM σ` -- computations with mutable state of type `σ`
* `IO` -- computations with real-world side effects

The `do`-notation makes monadic code readable and close to imperative style, while preserving the benefits of functional programming (purity, type safety, composability).
