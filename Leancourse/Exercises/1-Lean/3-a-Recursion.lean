import Mathlib

/-!
# 1.3-a -- Pattern matching and recursion

*Notes chapter 1.3, week 5.*

Sheet `1.1-a` defined functions on `ℕ` through the recursor. Here
you declare types of your own and define functions on them by
pattern matching: one branch for each constructor. Read *Inductive types*
in chapter 1.2 and chapter 1.3 first.

## Introduced here

| notation / tactic          | use it when                                  |
|----------------------------|----------------------------------------------|
| `inductive T where`        | declare a type by listing its constructors   |
| `def f : T → β` + branches | define `f` by one branch per constructor     |
| `induction t with`         | prove a statement for all `t : T`            |
| `simp only [f, h]`         | rewrite with the equations of `f` and `h`    |
| `dsimp only [f]`           | unfold `f`, apply `fun`s; nothing else       |
| `termination_by e`         | the recursion is on `e`, which must decrease |
| `decreasing_by omega`      | prove that it decreases                      |
| `rw [f]`                   | unfold `f` once, by its defining equation    |
| `simp [f]`                 | unfold `f` as often as needed and simplify   |
| `T.rec`                    | the recursor of an inductive type `T`        |
| `fun_induction f x with`   | induction along the branches of `f`          |

## Tactics from earlier sheets

| sheet   | tactics        |
|---------|----------------|
| `1.1-a` | `rfl`          |
| `1.1-b` | `cases`, `<;>` |
| `L-f`   | `have`         |
| `1.1-c` | `omega`        |
-/

/-! ## Part 1: A type with finitely many elements

The constructors are the elements. `open Weekday` lets you write
`mon` instead of `Weekday.mon`. -/

inductive Weekday where
  | mon | tue | wed | thu | fri | sat | sun

open Weekday

/-! A function on `Weekday` has one branch per constructor. On a
constructor it computes, so `rfl` checks it. -/

def Weekday.next : Weekday → Weekday
  | mon => tue
  | tue => wed
  | wed => thu
  | thu => fri
  | fri => sat
  | sat => sun
  | sun => mon

example : mon.next = tue := rfl

-- Exercise 1) Define `isWeekend`. The pattern `_` matches every
-- constructor not covered by an earlier branch.
def Weekday.isWeekend : Weekday → Bool
  | _ => sorry

-- Once exercise 1 is solved, uncomment:
-- example : sat.isWeekend = true := rfl
-- example : wed.isWeekend = false := rfl

-- Exercise 2) `d` is a variable, so `next` cannot compute. Split
-- into the seven constructors and let `rfl` do each.
example (d : Weekday) :
    d.next.next.next.next.next.next.next = d := by
  sorry

-- Exercise 3) After `cases d`, `simp [Weekday.isWeekend] at h ⊢`
-- computes `isWeekend` in `h` and in the goal. Where `h` becomes
-- `false = true`, the goal is closed.
example (d : Weekday) (h : d.isWeekend = true) :
    d = sat ∨ d = sun := by
  sorry

-- Exercise 4) Back to `Bool`. There are only four functions
-- `Bool → Bool`, so applying one three times is the same as applying
-- it once. Split on `b`, on `f true` (with `cases h1 : f true`) and
-- on `f false`; then `simp [h1, h2]` closes all eight goals.
example (f : Bool → Bool) (b : Bool) : f (f (f b)) = f b := by
  sorry

/-! ## Part 2: Binary trees

A tree is a leaf, or a node with a left tree, a label and a right
tree. The type occurs in the arguments of its own constructor: it is
recursive, like `ℕ`. This is the type `BinTree` from chapter 1.3. -/

inductive BinTree where
  | leaf : BinTree
  | node (l : BinTree) (a : ℕ) (r : BinTree) : BinTree

open BinTree

/-! A recursive function calls itself on the subtrees. That is
structural recursion, and Lean accepts it without further proof. -/

def BinTree.size : BinTree → ℕ
  | leaf => 0
  | node l _ r => l.size + 1 + r.size

def BinTree.leaves : BinTree → ℕ
  | leaf => 1
  | node l _ r => l.leaves + r.leaves

/-! `induction t` gives one goal per constructor, and for `node` one
induction hypothesis per subtree. `simp only [BinTree.leaves, ...]`
rewrites with the defining equations and the hypotheses; what is
left is arithmetic. -/

example (t : BinTree) : t.leaves = t.size + 1 := by
  induction t with
  | leaf => rfl
  | node l a r ihl ihr =>
    simp only [BinTree.leaves, BinTree.size, ihl, ihr]
    omega

/-! `dsimp only [BinTree.size]` unfolds with the same equations, and it
applies a `fun` to its argument. It uses only equations that hold by
definition, and it leaves the goal for you to look at instead of
trying to finish it. -/

example (l r : BinTree) (a : ℕ) :
    (node l a r).size = (fun n => n + 1) (l.size + r.size) := by
  dsimp only [BinTree.size]
  omega

-- Exercise 5) The sum of all labels.
def BinTree.sum : BinTree → ℕ
  | _ => sorry

-- Once exercise 5 is solved, uncomment:
-- example : (node (node leaf 1 leaf) 2 (node leaf 3 leaf)).sum = 6 :=
--   rfl

-- Exercise 6) The mirror image: left and right swapped, at every
-- node.
def BinTree.mirror : BinTree → BinTree
  | _ => sorry

-- Exercise 7) Like the worked example above.
example (t : BinTree) : t.mirror.size = t.size := by
  sorry

-- Exercise 8) Here `simp only` closes the goal by itself.
example (t : BinTree) : t.mirror.mirror = t := by
  sorry

/-! Every inductive type comes with a recursor, here `BinTree.rec`. It
takes a value for `leaf` and, for `node l a r`, a function of `l`,
`a`, `r` and of the two values already computed for `l` and `r`.
`#eval` cannot run a function defined with the recursor of your own
type, so it is marked `noncomputable`; `rfl` and `induction` work. -/

#check @BinTree.rec

-- Exercise 9) The size once more, now with the recursor. `sl` and
-- `sr` are the sizes of the two subtrees.
noncomputable def BinTree.size' (t : BinTree) : ℕ :=
  BinTree.rec sorry (fun _ _ _ sl sr => sorry) t

-- Exercise 10) By induction. In the `node` case, `simp only
-- [BinTree.size]`, then `rw [← ihl, ← ihr]`; what is left is `rfl`.
example (t : BinTree) : t.size' = t.size := by
  sorry

/-! ## Part 3: Recursion that is not structural

`n / 10` is smaller than `n`, but it is not a part of `n` in the
sense of a constructor, so the recursion is well-founded. Lean would
find the measure and the proof here on its own. We write both out,
to see what is proved: the measure (`termination_by n`) and why it
decreases (`decreasing_by`). The dependent `if _h : …` puts the
condition into the context, where `omega` finds it: here the goal is
`n / 10 < n` with `_h : ¬n < 10`. -/

def digits (n : ℕ) : ℕ :=
  if _h : n < 10 then 1 else 1 + digits (n / 10)
termination_by n
decreasing_by omega

-- Exercise 11) The sum of the decimal digits. Replace the `sorry`
-- after `decreasing_by`. What is the goal there?
def digitSum (n : ℕ) : ℕ :=
  if _h : n = 0 then 0 else n % 10 + digitSum (n / 10)
termination_by n
decreasing_by sorry

-- Exercise 12) The number of binary digits: `0` for `n = 0`,
-- otherwise one more than for `n / 2`. Write the whole definition,
-- with `termination_by` and `decreasing_by`.
def binLength (n : ℕ) : ℕ :=
  sorry

/-! Euclid's algorithm needs the help: `n % m < m` is not linear
arithmetic in `m`, so `omega` cannot prove it, and without
`decreasing_by` Lean rejects the definition. Two library theorems
help: `Nat.mod_lt (x : ℕ) : y > 0 → x % y < y` and
`Nat.pos_of_ne_zero : n ≠ 0 → 0 < n`. -/

-- Exercise 13) Replace the `sorry` after `decreasing_by`. Why does
-- the recursion stop?
def myGcd (m n : ℕ) : ℕ :=
  if _h : m = 0 then n else myGcd (n % m) m
termination_by m
decreasing_by sorry

/-! ## Part 4: Proving things about such functions

A function defined by well-founded recursion does not compute in
the kernel: `example : digits 1234 = 4 := rfl` fails (try it). Use
its defining equation instead. `rw [digits]` unfolds it once,
`simp [digits]` as often as needed. -/

example : digits 1234 = 4 := by
  simp [digits]

example (n : ℕ) (h : n < 10) : digits n = 1 := by
  rw [digits]
  simp [h]

-- Exercise 14)
example : digitSum 1234 = 10 := by
  sorry

-- Exercise 15)
example : binLength 37 = 6 := by
  sorry

-- Exercise 16)
example : myGcd 48 36 = 12 := by
  sorry

-- Exercise 17) `rw [myGcd]` unfolds once; then `simp`.
example (n : ℕ) : myGcd 0 n = n := by
  sorry

-- Exercise 18) Start with `rw [binLength]`. Then prove
-- `2 * n ≠ 0` and `2 * n / 2 = n` with `have` and `omega`, and give
-- both to `simp`.
example (n : ℕ) (h : 0 < n) :
    binLength (2 * n) = binLength n + 1 := by
  sorry

/-! ## Part 5: Induction along the definition

`induction n` gives a hypothesis for `n` when the goal is about
`n + 1`. A function such as `digits` calls itself on `n / 10`, so that
hypothesis is the wrong one. `fun_induction digits n` follows the
definition instead: one goal per branch, with `digits n` already
replaced by that branch, and one induction hypothesis per recursive
call. The cases are named `case1`, `case2`, … in the order of the
branches; each takes the variables and conditions of its branch, and
then the hypotheses. -/

example (n : ℕ) : digits n ≤ n + 1 := by
  fun_induction digits n with
  | case1 n h =>
    -- h : n < 10
    -- ⊢ 1 ≤ n + 1
    omega
  | case2 n h ih =>
    -- h : ¬n < 10
    -- ih : digits (n / 10) ≤ n / 10 + 1
    -- ⊢ 1 + digits (n / 10) ≤ n + 1
    omega

-- Exercise 19) In the first branch the condition `n = 0` is used up:
-- Lean replaces `n` by `0`, and `case1` takes no names.
example (n : ℕ) : digitSum n ≤ n := by
  sorry

-- Exercise 20) For your `binLength` from exercise 12.
example (n : ℕ) : binLength n ≤ n := by
  sorry

/-! Structural recursion works the same way. `fib` has three
branches, and the third calls itself twice, so `case3` has two
induction hypotheses. `induction n` would give only the one for
`n + 1`. -/

def fib : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | n + 2 => fib n + fib (n + 1)

-- Exercise 21) In `case3` the goal shows `2 ^ n.succ.succ`, which is
-- `2 ^ (n + 2)`. `omega` does not know powers: state
-- `2 ^ (n + 1) = 2 * 2 ^ n` and `2 ^ (n + 2) = 4 * 2 ^ n` with
-- `have … := by ring`, then `omega`. The first two cases: `simp`.
example (n : ℕ) : fib n ≤ 2 ^ n := by
  sorry

