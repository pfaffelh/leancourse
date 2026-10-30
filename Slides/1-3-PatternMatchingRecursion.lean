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
.reveal section img.tree { height: 190px; margin: 0.2em auto; }
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

def isEmpty' {α : Type*} (l : List α) : Bool :=
  match l with
  | []     => true
  | _ :: _ => false
```

# Structural recursion

A recursive call is _structural_ if its argument is a part of the input: an argument of the constructor that built it.

```lean -panel -stretch
def fib : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | n + 2 => fib n + fib (n + 1)

example : fib 3 = 2 := rfl
```

- `n + 2` is `succ (succ n)`; its parts are `succ n = n + 1` and `n`. Both calls are structural.
- `fib` computes by ι: `fib 3 ⟶ fib 1 + fib 2 ⟶ 1 + (fib 0 + fib 1) ⟶ 1 + (0 + 1)`.
- `def loop (n : ℕ) : ℕ := loop n + 1` is rejected. It would give `loop 0 = loop 0 + 1`; subtract `loop 0`: `0 = 1`.

# Are all cases covered?

`0` is `zero`, `1` is `succ zero`, `n + 2` is `succ (succ n)`. Lean turns the three patterns into two nested case splits:

```
fun x => Nat.casesOn x  (case 0)
  (fun m => Nat.casesOn m  (case 1)
    (fun n => (case n + 2)))
```

Every leaf of this tree must be reached by a pattern. Without the line for `1`:

```lean +error -panel -stretch
def fib' : ℕ → ℕ
  | 0 => 0
  | n + 2 => fib' n + fib' (n + 1)
```

:::class "key"
Lean reports "Missing cases: (Nat.succ Nat.zero)".
:::

# The recursor behind `fib`

```lean -panel -stretch
#print fib    -- fun x => Nat.brecOn x fib._f
```

`fib (n + 2)` needs two earlier values, `Nat.rec` hands over only one. `Nat.brecOn` is built from `Nat.rec` and hands over the values at _all_ smaller arguments. By hand, with `Nat.rec`: carry the pair `(fib n, fib (n + 1))`.

```lean -panel -stretch
def fibPair (n : ℕ) : ℕ × ℕ :=
  Nat.rec (0, 1) (fun _ p => (p.2, p.1 + p.2)) n

example : fibPair 10 = (55, 89) := rfl
```

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

The order comes from the type of the measure, by instance search:

```lean -panel -stretch
#synth WellFoundedRelation (ℕ × ℕ)
-- Prod.instWellFoundedRelation, defined as Prod.lex:
-- (a, b) < (c, d) iff a < c, or a = c and b < d
```

# Lean finds the measure

```lean -panel -stretch
def logb (b n : ℕ) : ℕ :=
  if h : 2 ≤ b ∧ b ≤ n then 1 + logb b (n / b)
  else 0
termination_by?
decreasing_by exact Nat.div_lt_self (by omega) h.1
```

`termination_by?` prints the measure Lean found: `n`. On `ℕ` the order is `<`. Lean cannot prove `n / b < n` by itself; `decreasing_by` gives the proof.

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

# An infinitely branching tree

A tree in which a node has one subtree for every natural number.

```lean -panel -stretch
inductive MyTree where
  | leaf : ℕ → MyTree
  | node : (ℕ → MyTree) → MyTree
```

{image "../static/figures/mytree.png" (class := "tree")}[The tree .node (fun n => if n = 0 then .node .leaf else .leaf n): a root node with subtrees labelled 0, 1, 2, 3, and so on; subtree 0 is a node whose subtrees are the leaves 0, 1, 2, 3, ...; subtrees 1, 2, 3 are the leaves 1, 2, 3]

- `leaf a`: a single leaf, carrying the number `a`; `leaf 7` is a tree.
- `node f`: a node with the subtrees `f 0`, `f 1`, `f 2`, …
- In `ℕ → MyTree`, the argument type of `node`, `MyTree` stands _right_ of `→`. Accepted.

# A negative occurrence

```
inductive Bad where
  | mk : (Bad → False) → Bad
-- error: (kernel) arg #1 of 'Bad.mk' has a non positive
--        occurrence of the datatypes being declared
```

Strict positivity: in argument types of constructors, the type occurs only _right_ of `→`. In `Bad → False`, `Bad` stands _left_ of `→`.

Suppose Lean accepted it. Every `b : Bad` is `mk f` for some `f : Bad → False`, so pattern matching takes `f` out again:

```
def unmk : Bad → (Bad → False)
  | .mk f => f          -- unmk (mk f) = f
```

:::class "key"
`mk : (Bad → False) → Bad` and `unmk : Bad → (Bad → False)`: so `Bad ↔ ¬Bad`.
:::

# False from nothing

```
def neg (b : Bad) : False := unmk b b
def boom : False := neg (Bad.mk neg)
```

- `neg b`: take the function stored in `b`, apply it to `b` itself. So `neg : Bad → False`.
- `Bad.mk neg : Bad`, and `neg` applied to it is a proof of `False`: no hypothesis, no axiom.

Lean checks the argument, with `mk` and `unmk` as hypotheses:

```lean -panel -stretch
example (Bad : Type) (mk : (Bad → False) → Bad)
    (unmk : Bad → (Bad → False)) : False :=
  let neg : Bad → False := fun b => unmk b b
  neg (mk neg)
```

:::class "key"
It loops: `neg (mk neg) ⟶ unmk (mk neg) (mk neg) ⟶ neg (mk neg)`.
:::

# Summary

- Pattern matching: one branch per constructor; Lean checks that every case is covered.
- Recursion must terminate. Structural recursion calls itself on parts of the argument and becomes the recursor.
- Well-founded recursion needs a measure that decreases; it is used through its equation lemmas, not `rfl`.
- The recursor of a type has one case per constructor, with a value of the motive for every recursive argument.
- Constructors must be strictly positive.
