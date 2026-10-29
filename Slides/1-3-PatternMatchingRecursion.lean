import VersoSlides
import Verso.Doc.Concrete
import Mathlib
import Slides.«1-2-FunctionsInductiveStructures»

open VersoSlides

set_option pp.rawOnError true

/-
Deck for the chapter "Pattern matching and recursion" of part 1 (Lean
and its type theory). It follows the chapter section by section:
pattern matching, structural and well-founded recursion, proofs about
recursive definitions, the recursor, strict positivity. It reopens the
namespace of the deck for chapter 1.2, whose `MyNat` it uses.
-/

namespace SlidesTypes
#doc (Slides) "Pattern matching and recursion" =>

```css
.reveal section p { font-size: 0.8em; line-height: 1.32; margin: 0.42em 0; }
.reveal section p.key, .reveal section .key p { color: #1b91ff; }
.reveal section table { font-size: 0.62em; margin: 0.2em auto 0.4em; }
.reveal section table th,
.reveal section table td { padding: 0.18em 0.9em; }
.reveal section li { font-size: 0.8em; }
.reveal section .math.display { font-size: 0.7em; }
.reveal section .small table, .reveal section table.small { font-size: 0.52em; }
.reveal section .small td, .reveal section table.small td { padding: 0.1em 0.8em; }
```

# Pattern matching and recursion

Lean and its type theory — chapter 3

:::class "key"
A function on an inductive type has one branch per constructor; Lean turns the branches into the recursor.
:::

# Pattern matching

One branch per constructor, each prefixed by `|`.

```lean -panel -stretch
def factorial : ℕ → ℕ
  | 0     => 1
  | n + 1 => (n + 1) * factorial n
```

Lean checks automatically:

- _exhaustiveness_: every constructor is covered,
- _termination_: `factorial n` is on a smaller argument.

# Matching on your own types

```lean -panel -stretch
def MyNat.double : MyNat → MyNat
  | .zero   => .zero
  | .succ n => .succ (.succ (MyNat.double n))

def MyNat.toNat : MyNat → ℕ
  | .zero   => 0
  | .succ n => MyNat.toNat n + 1

#eval (MyNat.double (.succ .zero)).toNat   -- 2
```

`m.toNat` means `MyNat.toNat m`.

:::class "key"
Pattern matching is translated into the recursor for the kernel, and into running code for `#eval`.
:::

# Lists

```
inductive List (α : Type u) where
  | nil : List α                    -- written []
  | cons (a : α) (l : List α) :
      List α                        -- written a :: l
```

```lean -panel -stretch
#eval (1 :: 2 :: 3 :: [] : List ℕ)   -- [1, 2, 3]
```

A list is empty, or a first element followed by a list. `[1, 2, 3]` is notation for `1 :: 2 :: 3 :: []`.

# Functions on lists

One branch per constructor; the pattern `_` matches anything. `match` does the same inside a term.

```lean -panel -stretch
def length' {α : Type*} : List α → ℕ
  | []      => 0
  | _ :: xs => 1 + length' xs

example (n : ℕ) : ℕ :=
  match n with
  | 0     => 42
  | _ + 1 => 0
```

# Recursion

```lean -panel -stretch
def fib : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | n + 2 => fib n + fib (n + 1)

example : fib 3 = 2 := rfl
```

- `fib (n + 2)` calls `fib n` and `fib (n + 1)`: smaller arguments. This is *structural recursion*.
- Lean checks this and translates `fib` into the recursor `Nat.rec` of 1.1. So `fib` computes by ι:
  `fib 3 ⟶ fib 1 + fib 2 ⟶ 1 + (fib 0 + fib 1) ⟶ 1 + (0 + 1)`.
- `def loop (n : ℕ) : ℕ := loop n + 1` is rejected. It would give `loop 0 = loop 0 + 1`; subtract `loop 0`: `0 = 1`.

# Termination by a measure

Cantor's diagonal enumeration of `ℕ × ℕ`. No argument shrinks in both calls; the pair (diagonal, position) does, lexicographically.

```lean -panel -stretch
def pairIndex : ℕ → ℕ → ℕ
  | 0, 0 => 0
  | 0, n + 1 => pairIndex n 0 + 1
  | m + 1, n => pairIndex m (n + 1) + 1
termination_by m n => (m + n, m)
decreasing_by all_goals (rw [Prod.lex_def]; omega)
```

Lean finds the measure `n`, but not the proof:

```lean -panel -stretch
def logb (b n : ℕ) : ℕ :=
  if h : 2 ≤ b ∧ b ≤ n then 1 + logb b (n / b)
  else 0
decreasing_by exact Nat.div_lt_self (by omega) h.1
```

# Proving things about recursive definitions

```lean -panel -stretch
def log2 (n : Nat) : Nat :=
  if 2 ≤ n then 1 + log2 (n / 2) else 0

example (n : ℕ) : fib (n + 2) = fib n + fib (n + 1) :=
  rfl
example : log2 16 = 4 := by simp [log2]
```

Structural recursion computes, so `rfl` works. Well-founded recursion does not: use the equation lemma `log2.eq_1`, via `rw [log2]`, `unfold log2` or `simp [log2]`.

# How the recursor is built

```
List.rec : {motive : List α → Sort u} →
  motive [] →                       -- case nil
  ((head : α) → (tail : List α) →
     motive tail →                  -- recursive argument
     motive (head :: tail)) →       -- case cons
  (t : List α) → motive t
```

- the motive `T → Sort u`: the type of the result
- one case per constructor: its arguments, and `motive aᵢ` for every argument `aᵢ : T`
- computation: `List.rec n c (a :: l) ⟶ c a l (List.rec n c l)`

:::class "key"
Read as a proof, `motive tail` is the induction hypothesis.
:::

# Strict positivity

```lean -panel -stretch
inductive MyTree where
  | leaf : ℕ → MyTree
  | node : (ℕ → MyTree) → MyTree
```

```
inductive Bad where
  | mk : (Bad → False) → Bad   -- rejected
```

The argument of `node` has type `ℕ → MyTree`: `MyTree` right of `→`. The argument of `Bad.mk` has type `Bad → False`: `Bad` left of `→`. With `Bad`, `neg b := app b b` gives `neg (Bad.mk neg) : False`.

:::class "key"
In the argument types of a constructor, the type may occur only to the right of an arrow.
:::

# Summary

- Pattern matching: one branch per constructor; Lean checks that every case is covered.
- Recursion must terminate. Structural recursion calls itself on parts of the argument and becomes the recursor.
- Well-founded recursion needs a measure that decreases; it is used through its equation lemmas, not `rfl`.
- The recursor of a type has one case per constructor, with a value of the motive for every recursive argument.
- Constructors must be strictly positive.
