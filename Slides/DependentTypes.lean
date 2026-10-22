import VersoSlides
import Verso.Doc.Concrete
import Mathlib

open VersoSlides

set_option pp.rawOnError true

/-
Deck for the chapter "Dependent Types in Depth" (Lean part, chapter 6).
It follows the chapter section by section: Pi and Sigma types, Sigma
against Exists, vectors and matrices, type families, subtypes, and why
dependent types matter. The code blocks are the chapter's own examples.
-/

namespace SlidesDependentTypes
#doc (Slides) "Dependent Types in Depth" =>

```css
.reveal section p { font-size: 0.8em; line-height: 1.32; margin: 0.42em 0; }
.reveal section p.key, .reveal section .key p { color: #1b91ff; }
.reveal section table { font-size: 0.62em; margin: 0.2em auto 0.4em; }
.reveal section table th,
.reveal section table td { padding: 0.18em 0.9em; }
.reveal section li { font-size: 0.8em; }
```

# Dependent Types in Depth

Lean and its type theory — chapter 6

:::class "key"
In Lean, types can depend on values.
:::

# What makes dependent types special

Simply typed (Haskell, OCaml): the output type depends only on the
_type_ of the input. `f : ℕ → ℕ` is fine, but not
"a list whose length equals `n`".

Dependently typed: the output type may mention the input _value_.

- `(n : ℕ) → Fin n → ℝ`
- `(n : ℕ) → Vector ℝ n`

:::class "key"
This lets Lean be a programming language and a theorem prover at once.
:::

# Pi types

The type of dependent functions: `(x : α) → β x`, with
`β : α → Sort u`. For each `a : α` the result has type `β a`.

If `β` does not depend on `x`, this is just `α → β`.
`∀` is the same thing when the codomain is a `Prop`:

```lean -panel -stretch
#check (∀ (n : ℕ), n = n)    -- Prop
#check ((n : ℕ) → n = n)     -- same Prop
```

# Pi types: two examples

```lean -panel -stretch
def allPositiveSucc : (n : ℕ) → 0 < n + 1 :=
  fun n => Nat.succ_pos n

def polyId : (α : Type) → α → α :=
  fun _ a => a

#check polyId ℕ 42         -- ℕ
#check polyId String "hi"  -- String
```

:::class "key"
The return type of `polyId` depends on its input.
:::

# Sigma types

The type of dependent pairs: `Σ (x : α), β x`, also written
`(x : α) × β x`. A term is `⟨a, b⟩` with `a : α` and `b : β a`.

```lean -panel -stretch
def exampleSigma : { n : ℕ // n % 2 = 0 } :=
  ⟨4, by norm_num⟩

#check exampleSigma.1   -- ℕ
#check exampleSigma.2   -- 4 % 2 = 0
```

If `β` does not depend on `x`, this is the product `α × β`.

# Sigma and Exists

:::table +colHeaders
*
  * type
  * lives in
  * the witness
*
  * `Σ (x : α), β x`
  * `Type`
  * can be extracted and computed with
*
  * `∃ (x : α), P x`
  * `Prop`
  * only usable inside proofs
:::

In `Prop` only truth matters, not the particular proof.
In `Type` the data matters.

Mathematically: `Σ` is a disjoint union, `∃` its propositional
truncation.

# Sigma or Exists in practice

```lean -panel -stretch
def sigmaExample : { n : ℕ // n > 5 } :=
  ⟨7, by norm_num⟩
#eval sigmaExample.1  -- 7

example : ∃ (n : ℕ), n > 5 := ⟨7, by norm_num⟩
```

- `∃` when only existence matters — typical in mathematics.
- `Σ` when you compute with the witness — typical in programming.

# Vectors indexed by length

A vector of length `n` over `α` is a function `Fin n → α`.

```lean -panel -stretch
def myVec : Fin 3 → ℕ := ![10, 20, 30]

#eval myVec 0   -- 10
#eval myVec 2   -- 30
```

:::class "key"
Index 5 of a 3-element vector does not exist: `5` is not a term of
type `Fin 3`. Out-of-bounds is a compile-time error.
:::

# Matrices

An `m × n` matrix is a function `Fin m → Fin n → α`, or
`Matrix (Fin m) (Fin n) α` in Mathlib.

```lean -panel -stretch
def myMatrix : Fin 2 → Fin 3 → ℕ :=
  ![![1, 2, 3], ![4, 5, 6]]

#eval myMatrix 0 1  -- 2
#eval myMatrix 1 2  -- 6
```

:::class "key"
`A * B` needs `m × n` times `n × p`. A dimension mismatch is a type error.
:::

# Type families

A type family is a function that returns a type.

```lean -panel -stretch
def BoolFamily : Bool → Type
  | true  => ℕ
  | false => String

def boolFamilyExample : (b : Bool) → BoolFamily b
  | true  => (42 : ℕ)
  | false => ("hello" : String)
```

# Fibers

The fiber of `f : α → β` over `b : β` is the subtype
`{a : α // f a = b}` — a type family indexed by `β`.

```lean -panel -stretch
def fiber (f : ℕ → ℕ) (b : ℕ) : Type :=
  {a : ℕ // f a = b}

def fiberExample : fiber (· * 2) 10 :=
  ⟨5, by norm_num⟩
```

# Subtypes

`{x : α // P x}` with `P : α → Prop`: a Sigma type whose second
component is a proof.

```lean -panel -stretch
def BigNat : Type := {n : ℕ // n > 5}

def seven : BigNat := ⟨7, by norm_num⟩
#eval seven.val  -- 7
```

:::class "key"
Proof irrelevance: two elements are equal iff their first components are.
:::

# Subtypes and sets

- Many Mathlib objects are subtypes, e.g. `{n : ℕ // Nat.Prime n}`.
- A set `s : Set α` selects elements, which keep their type `α`.
- The subtype `{x : α // P x}` is a _new_ type.
- `↥s` turns a set into the subtype of its members.

The chapter on sets and types spells this out.

# Why dependent types matter

- Length-indexed collections: no `head` of an empty list, matching
  matrix dimensions.
- Precise specifications: a sort whose type says the output is sorted
  and a permutation of the input.
- Theorems: a term of
  `∀ (n : ℕ), ∃ (p : ℕ), p > n ∧ Nat.Prime p` _is_ a proof of Euclid's
  theorem.
- Safe APIs: division that requires a proof of `b ≠ 0`.

# Safe division

```lean -panel -stretch
def safeDiv (a b : ℤ) (_hb : b ≠ 0) : ℤ :=
  a / b

#eval safeDiv 10 3 (by norm_num)
```

```lean +error -panel -stretch
#eval safeDiv 10 0 (by norm_num)
```

The caller must prove the denominator is nonzero.
No runtime exception is possible.

# Summary

- Pi types `(x : α) → β x`: dependent functions; `∀` is one.
- Sigma types `Σ (x : α), β x`: dependent pairs, in `Type`.
- `∃` is in `Prop`: the witness cannot be computed with.
- `Fin n → α`, `Fin m → Fin n → α`: sizes checked by the type.
- Type families and subtypes are everywhere in Mathlib.

:::class "key"
Type checking becomes undecidable in general. In return, the type
system is a logic in which we state and prove theorems.
:::
