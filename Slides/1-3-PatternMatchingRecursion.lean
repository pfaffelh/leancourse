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
recursive definitions, the recursor (with figures), `casesOn`,
course-of-values recursion, strict positivity. It reopens the
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
.reveal section img.tree { height: 185px; margin: 0 auto; }
.reveal section img.bintree { height: 240px; margin: 0 auto; }
.reveal section img.recgen { height: 405px; width: auto; max-width: none; margin: 0 auto; }
.reveal section img.casesfig { height: 470px; width: auto; max-width: none; margin: 0 auto; }
.reveal section img.recfig { height: 480px; width: auto; max-width: none; margin: 0 auto; }
.reveal section img.cantor { height: 260px; width: auto; max-width: none; flex: 0 0 auto; margin: 0; }
.reveal .r-hstack { align-items: center; justify-content: center; gap: 1.4rem; }
.reveal .r-hstack .r-vstack p { text-align: left; font-size: 0.66em; margin: 0.3em 0; }
```

# Pattern matching and recursion

Lean and its type theory — chapter 3

:::class "key"
We know the recursor already, here are more details.
:::

# Pattern matching

Recall: for an inductive type `α`, a function `α → β` is defined with the recursor `α.rec`. Pattern matching is a more convenient way to write it: one branch per constructor, each prefixed by `|`.

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

# Notation for lists

```
infixr:67 " :: " => List.cons       -- Lean's core library

syntax "[" term,* "]" : term        -- simplified
macro_rules
  | `([])          => `(List.nil)
  | `([$a])        => `(List.cons $a List.nil)
  | `([$a, $as,*]) => `(List.cons $a [$as,*])
```

`infixr` makes `::` a right-associative infix operator with binding power 67, so `1 :: 2 :: []` is `1 :: (2 :: [])`. `syntax` declares the bracket form, `macro_rules` rewrites it, one element at a time, into `List.cons` and `List.nil` (more in chapter 1.7).

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

# Two values back

`fib (n + 2)` needs two earlier values; `Nat.rec` hands over only one. By hand: carry the pair `(fib n, fib (n + 1))`.

`α × β`: the structure of pairs `(a, b)`, with fields `p.1 : α` and `p.2 : β` (chapter 1.4).

```lean -panel -stretch
def fibPair (n : ℕ) : ℕ × ℕ :=
  Nat.rec (0, 1) (fun _ p => (p.2, p.1 + p.2)) n

example : fibPair 10 = (55, 89) := rfl
```

:::class "key"
Lean's own translation of `fib` carries the values at _all_ smaller arguments (later in this deck).
:::

# How a recursor is built

{image "../static/figures/mynat_rec.png" (class := "recfig")}[Top: inductive MyNat where | zero : MyNat | succ (n : MyNat) : MyNat. Bottom: MyNat.rec with implicit motive : MyNat → Sort u, then (zero : motive MyNat.zero) → (succ : (n : MyNat) → motive n → motive (MyNat.succ n)) → (t : MyNat) → motive t. Arrows: the type MyNat gives the motive; constructor zero gives case zero; constructor succ gives case succ; its recursive argument n gives (n : MyNat) → motive n; the last line is the resulting function.]

`#check @MyNat.rec` omits the case names `zero`, `succ`.

# The recursor in general

{image "../static/figures/rec_general.png" (class := "recgen")}[Top: inductive T where | c₁ (b₁ : B₁) … (bₗ : Bₗ) (r₁ … rₖ : T) : T | …. Bottom: T.rec with implicit motive : T → Sort u, then the case f₁ : (b₁ : B₁) → … → (bₗ : Bₗ) → (r₁ … rₖ : T) → motive r₁ → … → motive rₖ → motive (c₁ b₁ … bₗ r₁ … rₖ), then the other cases and (t : T) → motive t. Arrows: the type gives the motive; constructor c₁ gives case f₁; its non-recursive arguments are passed on; its recursive arguments also give the values motive rⱼ; the other constructors give the other cases.]

`T.rec` has no body; the kernel knows it only by its ι-rules. With `R := T.rec f₁ … fₘ`:

```
R (c₁ b₁ … bₗ r₁ … rₖ)  ⟶  f₁ b₁ … bₗ r₁ … rₖ (R r₁) … (R rₖ)
```

# Example: `List.rec`

```
List.rec : {motive : List α → Sort u} →
  motive [] →                       -- case nil
  ((head : α) → (tail : List α) →
     motive tail →                  -- recursive argument
     motive (head :: tail)) →       -- case cons
  (t : List α) → motive t
```

- `nil` has no arguments; `cons` has `head : α` and the recursive argument `tail : List α`, so its case gets `motive tail`.
- Computation: `List.rec n c (a :: l) ⟶ c a l (List.rec n c l)`

:::class "key"
Read as a proof, `motive tail` is the induction hypothesis.
:::

# Case splits: `casesOn`

{image "../static/figures/mynat_casesOn.png" (class := "casesfig")}[Top: the declaration of MyNat. Bottom: MyNat.casesOn with implicit motive : MyNat → Sort u, then (t : MyNat), then (zero : motive MyNat.zero), then (succ : (n : MyNat) → motive (MyNat.succ n)), then motive t. Arrows as for MyNat.rec, but the recursive argument n gives only (n : MyNat), no value motive n.]

`casesOn t z s` only asks which constructor built `t`. It is `MyNat.rec z (fun n _ => s n) t`; for `ℕ`: `Nat.casesOn`.

# Are all cases covered?

Lean first writes the patterns of `fib` with constructors: `0` is `zero`, `1` is `succ zero`, `n + 2` is `succ (succ n)`. Then it splits from the outside in:

```
fun x => Nat.casesOn x  (case 0)          -- x = zero
  (fun m => Nat.casesOn m  (case 1)       -- x = succ m, m = zero
    (fun n => (case n + 2)))              -- x = succ (succ n)
```

So `1` is read in two steps: the outer split finds `succ`, the inner one finds `zero`. `#print fib.match_1` shows exactly this term.

:::class "key"
Every leaf must be reached by a pattern. Without the line for `1`: "Missing cases: (Nat.succ Nat.zero)".
:::

# Binary trees

```lean -panel -stretch
inductive BinTree where
  | leaf : BinTree
  | node (l : BinTree) (a : ℕ) (r : BinTree) : BinTree
```

{image "../static/figures/bintree.png" (class := "bintree")}[Three trees: .leaf of height 0; .node .leaf 4 .leaf of height 1; .node .leaf 3 (.node .leaf 4 .leaf) of height 2. Circles are nodes with their number, squares are leaves.]

- `BinTree` is the type of all finite binary trees; each element is one tree.
- `leaf`: a single leaf, no number. `node l a r`: root `a`, subtrees `l`, `r`.
- All leaves are the same term `.leaf`; only their positions differ.

# Height: recursion on both subtrees

```lean -panel -stretch
def BinTree.height : BinTree → ℕ
  | .leaf => 0
  | .node l _ r => max l.height r.height + 1

example : BinTree.leaf.height = 0 := rfl
example : (BinTree.node .leaf 4 .leaf).height = 1 := rfl
example : (BinTree.node .leaf 3
    (.node .leaf 4 .leaf)).height = 2 := rfl
```

`l` and `r` are parts of `.node l _ r`: both calls are structural.

# Termination by a measure

::::hstack
{image "../static/figures/cantor_pairing.png" (class := "cantor")}[Grid of the points (m, n) with m + n at most 4, labelled with their position in Cantor's enumeration; arrows run down each diagonal]

:::vstack
Cantor's enumeration of `ℕ × ℕ`: `pairIndex m n` is the position of `(m, n)`.

No argument shrinks in both calls. The pair `(m + n, m)`, diagonal and position, does.

Pairs are compared lexicographically: `(a, b) < (c, d)` iff `a < c`, or `a = c` and `b < d`.
:::
::::

```lean -panel -stretch
def pairIndex : ℕ → ℕ → ℕ
  | 0, 0 => 0
  | 0, n + 1 => pairIndex n 0 + 1
  | m + 1, n => pairIndex m (n + 1) + 1
termination_by m n => (m + n, m)
decreasing_by all_goals (rw [Prod.lex_def]; omega)
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

# Course-of-values recursion

`fib (n + 2)` needs `fib (n + 1)` _and_ `fib n`, the recursor hands over only one value. Lean's translation passes a table of _all_ smaller values (`Nat.brecOn`; `#print fib` shows it). Carrying the pair by hand, as in `fibPair`, also makes `#eval` fast:

```
#eval fib 30                 -- 0.6 s
#eval fib 32                 -- 1.7 s: about 7 million calls
#eval (fibPair 32).1         -- immediate: 32 steps
#eval (fibPair 10000).1      -- immediate, 2090 digits
```

`#eval` runs `fib` as written: every call makes two more, so the time grows like `fib n` itself, by a factor of about 1.6 per step.

# Two steps back in proofs

The same works with a `Prop`-valued motive: a proof may use the statement for _all_ smaller arguments, here two steps back.

```lean -panel -stretch
theorem fib_pos : (n : ℕ) → 0 < fib (n + 1)
  | 0 => by decide
  | 1 => by decide
  | n + 2 => by
      have h := fib_pos n     -- two steps back
      show 0 < fib (n + 1) + fib (n + 2)
      omega
```

# An infinitely branching tree

`MyTree` is a type; its elements are trees. Every path ends in a leaf.

```lean -panel -stretch
inductive MyTree where
  | leaf (a : ℕ) : MyTree
  | node (f : ℕ → MyTree) : MyTree
```

{image "../static/figures/mytree.png" (class := "tree")}[The tree .node (fun n => if n = 0 then .node .leaf else .leaf n): a root node with subtrees labelled 0, 1, 2, 3, and so on; subtree 0 is a node whose subtrees are the leaves 0, 1, 2, 3, ...; subtrees 1, 2, 3 are the leaves 1, 2, 3]

- `leaf a`: the tree that is a single leaf, carrying the number `a`.
- `node f`: the tree whose root has the subtrees `f 0`, `f 1`, `f 2`, …
- In the type `ℕ → MyTree` of `f`, `MyTree` stands _right_ of `→`. Accepted.

# A negative occurrence

```
inductive Bad where
  | mk (f : Bad → False) : Bad
-- error: (kernel) arg #1 of 'Bad.mk' has a non positive
--        occurrence of the datatypes being declared
```

Strict positivity: in argument types of constructors, the type occurs only _right_ of `→`. In the type `Bad → False` of `f`, `Bad` stands _left_ of `→`.

If Lean accepted it, we would have `mk` and, by pattern matching `| .mk f => f`, its inverse `unmk`. Then:

```lean -panel -stretch
example (Bad : Type) (mk : (Bad → False) → Bad)
    (unmk : Bad → (Bad → False)) : False := by
  have neg : Bad → False := fun b => unmk b b
  have b : Bad := mk neg
  exact neg b
```

# Why positivity is enough

Read in sets, the declared type `X` satisfies `X = F(X)`:

:::table +colHeaders +rowSeps
*
  * declaration
  * equation
*
  * `ℕ`
  * `X = {0} ⊔ X`
*
  * `MyTree`
  * `X = ℕ ⊔ (ℕ → X)`
*
  * `Bad`
  * `X = (X → ∅)`
:::

- `X` only right of `→`: `F` is monotone. The stages `∅ ⊆ F(∅) ⊆ F(F(∅)) ⊆ …`, continued transfinitely, reach a fixed point: a set that is the type.
- `X → ∅` has one element if `X = ∅`, none otherwise: no solution, `Bad ↔ ¬Bad`.
- With `X → Bool` instead: `X` would contain its power set. Cantor.

:::class "key"
Proved for inductive types: Aczel 1977, Dybjer 1991; for the CIC: Werner 1997; for Lean, checked in Lean: Con-Leche (Breitner).
:::

# Summary

- Pattern matching: one branch per constructor; Lean checks that every case is covered.
- Recursion must terminate. Structural recursion calls itself on parts of the argument and becomes the recursor.
- Well-founded recursion needs a measure that decreases; it is used through its equation lemmas, not `rfl`.
- The recursor of a type has one case per constructor, with a value of the motive for every recursive argument.
- Pattern matching becomes `casesOn`; structural recursion passes the values at all smaller arguments (`brecOn`, Project 7).
- Constructors must be strictly positive.
