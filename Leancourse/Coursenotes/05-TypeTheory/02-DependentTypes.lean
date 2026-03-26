import VersoManual
import Manual.Meta
import Leancourse.Misc.Defs
import Mathlib

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open MyDef

set_option pp.rawOnError true

#doc (Manual) "Dependent Types in Depth" =>
%%%
htmlSplit := .never
tag := "dependent-types"
%%%

Dependent types are the feature that distinguishes Lean's type system from those of most mainstream programming languages. In a dependently typed language, **types can depend on values**. This single idea has far-reaching consequences: it allows us to express precise specifications, encode mathematical statements, and catch entire classes of errors at compile time.

# What makes dependent types special
%%%
tag := "what-dependent-types"
%%%

In a simply typed language (like Haskell without extensions, or basic OCaml), the type of a function's output cannot depend on the *value* of its input -- only on the *type* of its input. For example, you can write `f : ℕ → ℕ`, but you cannot write a type that says "a list whose length equals the input `n`."

In a dependently typed language, you *can* do this. The type of the output may mention the input value. For example:

- `(n : ℕ) → Fin n → ℝ` is the type of a function that takes a natural number `n` and then an element of `{0, 1, ..., n-1}`, returning a real number.
- `(n : ℕ) → Vector ℝ n` is the type of a function that, given `n`, returns a vector of `n` real numbers.

This expressiveness is what allows Lean to serve simultaneously as a programming language and a theorem prover.

# Pi types: dependent function types
%%%
tag := "pi-types"
%%%

The **Pi type** (also written Π-type) is the type of dependent functions. In Lean, we write it as:

`(x : α) → β x`

where `β : α → Sort u` is a type family indexed by `α`. For each value `a : α`, the function returns a term of type `β a`. When `β` does not actually depend on `x`, this reduces to the ordinary function type `α → β`.

In Lean, `∀` is notation for Pi types when the codomain is a `Prop`:

```lean
-- These are the same:
#check (∀ (n : ℕ), n = n)        -- Prop
#check ((n : ℕ) → n = n)         -- same Prop
```

Here is a concrete example of a dependent function:

```lean
-- A function that returns a proof depending on the input
def allPositiveSucc : (n : ℕ) → 0 < n + 1 :=
  fun n => Nat.succ_pos n
```

Another important example: a function that, given a type, returns the identity function on that type. This is a function whose *return type depends on its input*:

```lean
def polyId : (α : Type) → α → α :=
  fun _ a => a

#check polyId ℕ 42       -- ℕ
#check polyId String "hi" -- String
```

# Sigma types: dependent pair types
%%%
tag := "sigma-types"
%%%

The **Sigma type** (also written Σ-type) is the type of dependent pairs. In Lean, we write:

`Σ (x : α), β x`

or equivalently `(x : α) × β x`. A term of this type is a pair `⟨a, b⟩` where `a : α` and `b : β a`. Note that the type of the second component depends on the *value* of the first component.

```lean
-- A dependent pair: a natural number together with a proof it is even
def exampleSigma : { n : ℕ // n % 2 = 0 } :=
  ⟨4, by norm_num⟩

-- Accessing the components
#check exampleSigma.1   -- ℕ
#check exampleSigma.2   -- 4 % 2 = 0
```

When `β` does not depend on `x`, the Sigma type reduces to the ordinary product type `α × β`.

# Difference between Sigma and Exists
%%%
tag := "sigma-vs-exists"
%%%

This is a subtle but important distinction in Lean:

- `Σ (x : α), β x` lives in `Type` -- you can extract the witness and use it computationally.
- `∃ (x : α), P x` lives in `Prop` -- the witness is "erased" and cannot be used in computations (only in proofs).

This reflects the principle of **proof irrelevance**: in `Prop`, the specific proof does not matter, only whether the proposition is true or false. In `Type`, the data matters.

```lean
-- Sigma: we can extract the witness
def sigmaExample : { n : ℕ // n > 5 } := ⟨7, by norm_num⟩
#eval sigmaExample.1  -- 7

-- Exists: we CANNOT extract the witness for computation
-- (we can only use it inside proofs)
example : ∃ (n : ℕ), n > 5 := ⟨7, by norm_num⟩
```

Mathematically, `Σ` is like a disjoint union (indexed coproduct), while `∃` is the propositional truncation thereof. In practice:
- Use `∃` when you only need to know that a witness *exists* (typical in mathematics).
- Use `Σ` when you need to actually *compute with* the witness (typical in programming).

# Vectors indexed by length
%%%
tag := "vectors-indexed"
%%%

A classic example of dependent types is the type of vectors (lists of a fixed length). In Mathlib, one way to represent a vector of length `n` with entries in `α` is as a function `Fin n → α`, where `Fin n` is the type with exactly `n` elements `{0, 1, ..., n-1}`.

```lean
-- A vector of 3 natural numbers, represented as a function from Fin 3
def myVec : Fin 3 → ℕ := ![10, 20, 30]

#eval myVec 0   -- 10
#eval myVec 1   -- 20
#eval myVec 2   -- 30
```

The advantage of this representation is that indexing is *always safe*: you cannot access index 5 of a 3-element vector, because `5` is not a term of type `Fin 3`. The type system prevents out-of-bounds errors at compile time.

# Matrices as dependent types
%%%
tag := "matrices-dependent"
%%%

Matrices are a natural extension. An `m × n` matrix with entries in `α` can be represented as a function `Fin m → Fin n → α`, or equivalently as `Matrix (Fin m) (Fin n) α` in Mathlib:

```lean
-- A 2×3 matrix of natural numbers
def myMatrix : Fin 2 → Fin 3 → ℕ :=
  ![![1, 2, 3], ![4, 5, 6]]

#eval myMatrix 0 1  -- 2
#eval myMatrix 1 2  -- 6
```

In Mathlib, matrix multiplication is only defined when the dimensions match. If `A` is an `m × n` matrix and `B` is an `n × p` matrix, then `A * B` is an `m × p` matrix. The dependent types enforce that the inner dimensions agree -- a dimension mismatch is a *type error*, caught at compile time.

# Type families
%%%
tag := "type-families"
%%%

A **type family** is simply a function that returns a type. Type families are pervasive in Lean and Mathlib:

```lean
-- A simple type family indexed by Bool
def BoolFamily : Bool → Type
  | true  => ℕ
  | false => String

-- Dependent function using the type family
def boolFamilyExample : (b : Bool) → BoolFamily b
  | true  => (42 : ℕ)
  | false => ("hello" : String)
```

In mathematical formalization, type families appear everywhere. For instance, the fiber of a function `f : α → β` over a point `b : β` is the subtype `{a : α // f a = b}`, which is a type family indexed by `β`.

```lean
-- The fiber of a function as a type family
def fiber (f : ℕ → ℕ) (b : ℕ) : Type :=
  {a : ℕ // f a = b}

-- An element of the fiber of (· * 2) over 10
def fiberExample : fiber (· * 2) 10 :=
  ⟨5, by norm_num⟩
```

# Subtypes
%%%
tag := "subtypes"
%%%

The **subtype** `{x : α // P x}` is a special case of a Sigma type where `P : α → Prop`. It represents elements of `α` satisfying predicate `P`. Since the second component is a proof (in `Prop`), subtypes enjoy proof irrelevance: two elements of `{x : α // P x}` are equal if and only if their first components are equal.

```lean
-- The type of natural numbers greater than 5
def BigNat : Type := {n : ℕ // n > 5}

def seven : BigNat := ⟨7, by norm_num⟩
def ten : BigNat := ⟨10, by norm_num⟩

-- We can extract the value
#eval seven.val  -- 7
```

This is how many mathematical objects are defined in Mathlib. For example, the type of prime numbers could be defined as `{n : ℕ // Nat.Prime n}`.

# Why dependent types matter
%%%
tag := "why-dependent-types"
%%%

Dependent types make Lean strictly more expressive than simply-typed languages like Haskell or OCaml. Here are some things you can express with dependent types that you cannot express in simply-typed languages:

1. **Length-indexed collections**: The type system guarantees that `head` is never called on an empty list, that matrix dimensions match in multiplication, etc.

2. **Precise specifications**: You can write a sorting function whose *type* guarantees that the output is sorted and is a permutation of the input.

3. **Mathematical theorems**: The type `∀ (n : ℕ), ∃ (p : ℕ), p > n ∧ Nat.Prime p` expresses Euclid's theorem (infinitely many primes). A term of this type *is* a proof.

4. **Safe APIs**: You can define a division function `(a : ℤ) → (b : ℤ) → b ≠ 0 → ℤ` that *requires* a proof of non-zero denominator. No runtime exceptions possible.

```lean
-- Safe division: the caller must prove the denominator is nonzero
def safeDiv (a b : ℤ) (hb : b ≠ 0) : ℤ :=
  a / b

-- This works:
#eval safeDiv 10 3 (by norm_num)

-- This would be a type error (uncomment to see):
-- #eval safeDiv 10 0 (by norm_num)  -- norm_num cannot prove 0 ≠ 0
```

The price of this expressiveness is that type checking becomes undecidable in general (though Lean uses various heuristics to make it practical). But for mathematics, the payoff is enormous: the type system itself becomes a logic in which we can state and prove theorems.
