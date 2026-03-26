import VersoManual
import Manual.Meta
import Leancourse.Misc.Defs
import Mathlib

open Verso.Genre Manual
open MyDef

set_option pp.rawOnError true

#doc (Manual) "Basics of Functional Programming" =>
%%%
htmlSplit := .never
tag := "fp-basics"
%%%

In this chapter, we introduce the fundamentals of functional programming in Lean. If you have a background in mathematics but not in programming, do not worry: functional programming is in many ways closer to mathematics than imperative programming (like Python or Java). The central idea is that programs are built from *functions* in the mathematical sense -- they take inputs and produce outputs, without hidden side effects.

# Pure functions
%%%
tag := "pure-functions"
%%%

A *pure function* is one whose output depends only on its inputs. Given the same arguments, it always returns the same result. This is exactly how functions work in mathematics: if `f(x) = x + 1`, then `f(3)` is always `4`.

In Lean, we define functions using `def`:

```lean
def double (n : ℕ) : ℕ := 2 * n
```

We can evaluate functions using `#eval`:

```lean
#eval double 5    -- outputs 10
#eval double 0    -- outputs 0
```

Functions can take multiple arguments. Lean uses *currying*: a function of two arguments is really a function that takes one argument and returns another function.

```lean
def add (a b : ℕ) : ℕ := a + b

#eval add 3 4    -- outputs 7
```

The type of `add` is `ℕ → ℕ → ℕ`, which is read as `ℕ → (ℕ → ℕ)`. So `add 3` is itself a function of type `ℕ → ℕ`.

# Anonymous functions
%%%
tag := "anonymous-functions"
%%%

Sometimes we need a quick, throwaway function without giving it a name. We use `fun` (short for "function") with the `↦` arrow (typed `\mapsto`):

```lean
#eval (fun x : ℕ ↦ x + 1) 5       -- outputs 6
#eval (fun x y : ℕ ↦ x * y) 3 4   -- outputs 12
```

Anonymous functions are particularly useful when passing functions as arguments to other functions. In mathematics, one would write `x \mapsto x^2`; in Lean, we write `fun x ↦ x ^ 2`.

# Inductive types
%%%
tag := "inductive-types"
%%%

One of the most powerful features of Lean is the ability to define new types using `inductive`. An inductive type is defined by listing its *constructors* -- the ways to build values of that type.

The natural numbers are the prototypical example. Mathematically, the natural numbers are characterized by: (1) `0` is a natural number, and (2) if `n` is a natural number, then `succ n` (the successor of `n`) is a natural number. In Lean, one would write:

```lean
inductive MyNat where
  | zero : MyNat
  | succ : MyNat → MyNat
```

This says: `MyNat` has exactly two constructors. Every value of type `MyNat` is either `MyNat.zero` or `MyNat.succ n` for some `n : MyNat`.

Here is another example -- a type representing a binary tree of natural numbers:

```lean
inductive Tree where
  | leaf : Tree
  | node : Tree → ℕ → Tree → Tree
```

A `Tree` is either a `leaf` (an empty tree) or a `node` consisting of a left subtree, a value, and a right subtree.

We can also define our own version of lists:

```lean
inductive MyList (α : Type) where
  | nil : MyList α
  | cons : α → MyList α → MyList α
```

This says: a list of `α` values is either empty (`nil`) or formed by prepending an element to an existing list (`cons`).

# Pattern matching and `match`
%%%
tag := "pattern-matching"
%%%

Once we have inductive types, we need a way to *use* them. Pattern matching lets us define functions by specifying what to do for each constructor:

```lean
def isZero (n : Nat) : Bool :=
  match n with
  | Nat.zero => true
  | Nat.succ _ => false

#eval isZero 0       -- outputs true
#eval isZero 42      -- outputs false
```

The `match` expression looks at which constructor was used to build the value, and runs the corresponding branch. The underscore `_` means "I do not care about this argument."

We can also pattern match on multiple arguments simultaneously:

```lean
def myAnd (a b : Bool) : Bool :=
  match a, b with
  | true, true => true
  | _, _ => false

#eval myAnd true true     -- outputs true
#eval myAnd true false    -- outputs false
```

# Recursion and structural recursion
%%%
tag := "recursion"
%%%

Many functions on inductive types are naturally *recursive*: they call themselves on smaller values. For the natural numbers, a recursive function processes `succ n` by making a recursive call on `n`. Lean uses *structural recursion*: it checks that every recursive call is made on a structurally smaller argument (a sub-term of the input), which guarantees termination.

```lean
def factorial : ℕ → ℕ
  | 0 => 1
  | n + 1 => (n + 1) * factorial n

#eval factorial 5    -- outputs 120
#eval factorial 10   -- outputs 3628800
```

Note the concise syntax: instead of using `match`, we pattern-match directly after the function name. This is purely a stylistic choice.

Here is a function computing the length of a list:

```lean
def myLength {α : Type} : List α → ℕ
  | [] => 0
  | _ :: xs => 1 + myLength xs

#eval myLength [1, 2, 3, 4]    -- outputs 4
```

And here is a function that sums all the values in a `Tree`:

```lean
def Tree.sum : Tree → ℕ
  | Tree.leaf => 0
  | Tree.node l v r => Tree.sum l + v + Tree.sum r

#eval Tree.sum (Tree.node (Tree.node Tree.leaf 3 Tree.leaf) 5 Tree.leaf)
-- outputs 8
```

An important example from mathematics is the Fibonacci sequence:

```lean
def fib : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | n + 2 => fib n + fib (n + 1)

#eval fib 10    -- outputs 55
```

# Higher-order functions
%%%
tag := "higher-order-functions"
%%%

A *higher-order function* is one that takes a function as an argument or returns a function as a result. This is one of the central ideas of functional programming, and it is also very natural mathematically. For instance, the derivative is a higher-order function: it takes a function and returns a function.

The three most important higher-order functions on lists are `map`, `filter`, and `foldl` (also known as `fold`).

**`List.map`** applies a function to every element of a list:

```lean
#eval [1, 2, 3, 4].map (fun x ↦ x * x)    -- outputs [1, 4, 9, 16]
#eval [1, 2, 3].map (· + 10)               -- outputs [11, 12, 13]
```

Note the `·` notation: `(· + 10)` is shorthand for `(fun x ↦ x + 10)`.

**`List.filter`** keeps only the elements satisfying a predicate:

```lean
#eval [1, 2, 3, 4, 5, 6].filter (fun x ↦ x % 2 == 0)    -- outputs [2, 4, 6]
```

**`List.foldl`** combines all elements of a list using a binary operation and an initial value. It "folds" the list from the left:

```lean
#eval [1, 2, 3, 4].foldl (· + ·) 0        -- outputs 10 (sum)
#eval [1, 2, 3, 4].foldl (· * ·) 1        -- outputs 24 (product)
```

We can define our own higher-order functions. For example, here is a function that applies a function `n` times:

```lean
def iterate {α : Type} (f : α → α) : ℕ → α → α
  | 0, x => x
  | n + 1, x => f (iterate f n x)

#eval iterate (· + 1) 5 0        -- outputs 5
#eval iterate (· * 2) 4 1        -- outputs 16
```

We can also write a function that composes two functions:

```lean
def myCompose {α β γ : Type} (g : β → γ) (f : α → β) : α → γ :=
  fun x ↦ g (f x)

#eval myCompose (· + 1) (· * 2) 3    -- outputs 7
```

In Lean, function composition is available as `Function.comp` or simply as `∘` (typed `\circ`).

# Summary
%%%
tag := "fp-basics-summary"
%%%

Functional programming in Lean is built on a few core ideas:

* **Pure functions**: outputs depend only on inputs.
* **Inductive types**: define new types by specifying constructors.
* **Pattern matching**: define functions by cases on the constructors.
* **Structural recursion**: define recursive functions that provably terminate.
* **Higher-order functions**: pass functions as arguments or return them.

These ideas align closely with mathematical practice: inductive types correspond to inductively defined sets, pattern matching corresponds to case analysis, and recursion corresponds to inductive definitions.
