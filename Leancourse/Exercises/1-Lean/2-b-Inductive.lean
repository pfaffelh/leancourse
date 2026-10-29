import Mathlib

/-!
# 1.2-b -- Inductive types, pattern matching, recursion, `Fin`

*Notes chapter 1.2, week 4.*

Sheet `1.1-a` defined functions on `ℕ` through the recursor. Here
you declare types of your own and define functions on them by
pattern matching: one branch for each constructor. Read the sections
*Inductive types*, *Structures*, *Pattern matching*, *Recursion
and termination* and *Proving things about recursive definitions*
of chapter 1.2 first.

## Introduced here

| notation / tactic          | use it when                                  |
|----------------------------|----------------------------------------------|
| `inductive T where`        | declare a type by listing its constructors   |
| `def f : T → β` + branches | define `f` by one branch per constructor     |
| `induction t with`         | prove a statement for all `t : T`            |
| `simp only [f, h]`         | rewrite with the equations of `f` and `h`    |
| `termination_by e`         | the recursion is on `e`, which must decrease |
| `decreasing_by omega`      | prove that it decreases                      |
| `rw [f]`                   | unfold `f` once, by its defining equation    |
| `simp [f]`                 | unfold `f` as often as needed and simplify   |
| `⟨i, h⟩ : Fin n`           | build an element from `i` and `h : i < n`    |
| `Fin.ext`                  | prove `a = b` from `a.val = b.val`           |

`cases`, `<;>` and `rfl` are known from `1.1-b`, `omega` and `simp`
from `1.1-c`.
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

/-! ## Part 2: Binary trees

A tree is a leaf, or a node with a left tree, a label and a right
tree. The type occurs in the arguments of its own constructor: it is
recursive, like `ℕ`. (`Tree` is taken in Mathlib, hence `MyTree`.) -/

inductive MyTree where
  | leaf : MyTree
  | node : MyTree → ℕ → MyTree → MyTree

open MyTree

/-! A recursive function calls itself on the subtrees. That is
structural recursion, and Lean accepts it without further proof. -/

def MyTree.size : MyTree → ℕ
  | leaf => 0
  | node l _ r => l.size + 1 + r.size

def MyTree.leaves : MyTree → ℕ
  | leaf => 1
  | node l _ r => l.leaves + r.leaves

/-! `induction t` gives one goal per constructor, and for `node` one
induction hypothesis per subtree. `simp only [MyTree.leaves, ...]`
rewrites with the defining equations and the hypotheses; what is
left is arithmetic. -/

example (t : MyTree) : t.leaves = t.size + 1 := by
  induction t with
  | leaf => rfl
  | node l a r ihl ihr =>
    simp only [MyTree.leaves, MyTree.size, ihl, ihr]
    omega

-- Exercise 4) The sum of all labels.
def MyTree.sum : MyTree → ℕ
  | _ => sorry

-- Once exercise 4 is solved, uncomment:
-- example : (node (node leaf 1 leaf) 2 (node leaf 3 leaf)).sum = 6 :=
--   rfl

-- Exercise 5) The mirror image: left and right swapped, at every
-- node.
def MyTree.mirror : MyTree → MyTree
  | _ => sorry

-- Exercise 6) Like the worked example above.
example (t : MyTree) : t.mirror.size = t.size := by
  sorry

-- Exercise 7) Here `simp only` closes the goal by itself.
example (t : MyTree) : t.mirror.mirror = t := by
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

-- Exercise 8) The sum of the decimal digits. Replace the `sorry`
-- after `decreasing_by`. What is the goal there?
def digitSum (n : ℕ) : ℕ :=
  if _h : n = 0 then 0 else n % 10 + digitSum (n / 10)
termination_by n
decreasing_by sorry

-- Exercise 9) The number of binary digits: `0` for `n = 0`,
-- otherwise one more than for `n / 2`. Write the whole definition,
-- with `termination_by` and `decreasing_by`.
def binLength (n : ℕ) : ℕ :=
  sorry

/-! Euclid's algorithm needs the help: `n % m < m` is not linear
arithmetic in `m`, so `omega` cannot prove it, and without
`decreasing_by` Lean rejects the definition. Two library theorems
help: `Nat.mod_lt (x : ℕ) : y > 0 → x % y < y` and
`Nat.pos_of_ne_zero : n ≠ 0 → 0 < n`. -/

-- Exercise 10) Replace the `sorry` after `decreasing_by`. Why does
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

-- Exercise 11)
example : digitSum 1234 = 10 := by
  sorry

-- Exercise 12)
example : binLength 37 = 6 := by
  sorry

-- Exercise 13)
example : myGcd 48 36 = 12 := by
  sorry

-- Exercise 14) `rw [myGcd]` unfolds once; then `simp`.
example (n : ℕ) : myGcd 0 n = n := by
  sorry

-- Exercise 15) Start with `rw [binLength]`. Then prove
-- `2 * n ≠ 0` and `2 * n / 2 = n` with `have` and `omega`, and give
-- both to `simp`.
example (n : ℕ) (h : 0 < n) :
    binLength (2 * n) = binLength n + 1 := by
  sorry

/-! ## Part 5: `Fin n`, a structure with a proof

An element of `Fin n` is a pair `⟨i, h⟩` of a number `i : ℕ` and a
proof `h : i < n`. The fields are `val` and `isLt`. Two elements are
equal when their values are: `Fin.ext : a.val = b.val → a = b`.
`omega` knows that `i.val < n` for `i : Fin n`. Read *Data with a
property* in chapter 1.2.

Fill in each definition. The `example` below it should then be
provable by `rfl` (by `decide` for Exercise 19). -/

example : Fin 3 := ⟨2, by decide⟩

-- Exercise 16)
def two : Fin 5 := sorry

example : two.val = 2 := by
  sorry

-- Exercise 17) The largest element of `Fin (n + 1)`.
def myLast (n : ℕ) : Fin (n + 1) := sorry

example (n : ℕ) : myLast n = Fin.last n := by
  sorry

-- Exercise 18) `Fin n` sits inside `Fin (n + 1)`.
def embed {n : ℕ} (i : Fin n) : Fin (n + 1) := sorry

example : (embed (2 : Fin 3)).val = 2 := by
  sorry

-- Exercise 19) Counting from the other end: `0 ↦ n - 1`,
-- `1 ↦ n - 2`, and so on.
def rev {n : ℕ} (i : Fin n) : Fin n := sorry

example : rev (1 : Fin 5) = 3 := by
  sorry

-- Exercise 20) Start with `apply Fin.ext`, then `simp only [rev]`
-- and `omega`.
example {n : ℕ} (i : Fin n) : rev (rev i) = i := by
  sorry

/-! ## Part 6: A dependent function

`ZMod n` is ℤ/nℤ. The function `natSelf` sends `n` to the class of
`n` in ℤ/nℤ. -/

def natSelf : (n : ℕ) → ZMod n := fun n => n

-- Exercise 21) Compute `natSelf 6`, then prove it. What is
-- `natSelf n` for every `n`, and why does that not make `natSelf`
-- a constant function?
example : natSelf 6 = 0 := by
  sorry
