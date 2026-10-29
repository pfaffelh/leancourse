import Mathlib

/-!
# (witness) 1.2-b -- Inductive types, pattern matching, recursion

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

/-! ## Part 1: A type with finitely many elements -/

inductive Weekday where
  | mon | tue | wed | thu | fri | sat | sun

open Weekday

def Weekday.next : Weekday → Weekday
  | mon => tue
  | tue => wed
  | wed => thu
  | thu => fri
  | fri => sat
  | sat => sun
  | sun => mon

example : mon.next = tue := rfl

def Weekday.isWeekend : Weekday → Bool
  | sat => true
  | sun => true
  | _ => false

example : sat.isWeekend = true := rfl
example : wed.isWeekend = false := rfl

example (d : Weekday) :
    d.next.next.next.next.next.next.next = d := by
  cases d <;> rfl

example (d : Weekday) (h : d.isWeekend = true) :
    d = sat ∨ d = sun := by
  cases d <;> simp [Weekday.isWeekend] at h ⊢

/-! ## Part 2: Binary trees -/

inductive MyTree where
  | leaf : MyTree
  | node : MyTree → ℕ → MyTree → MyTree

open MyTree

def MyTree.size : MyTree → ℕ
  | leaf => 0
  | node l _ r => l.size + 1 + r.size

def MyTree.leaves : MyTree → ℕ
  | leaf => 1
  | node l _ r => l.leaves + r.leaves

example (t : MyTree) : t.leaves = t.size + 1 := by
  induction t with
  | leaf => rfl
  | node l a r ihl ihr =>
    simp only [MyTree.leaves, MyTree.size, ihl, ihr]
    omega

def MyTree.sum : MyTree → ℕ
  | leaf => 0
  | node l a r => l.sum + a + r.sum

example : (node (node leaf 1 leaf) 2 (node leaf 3 leaf)).sum = 6 :=
  rfl

def MyTree.mirror : MyTree → MyTree
  | leaf => leaf
  | node l a r => node r.mirror a l.mirror

example (t : MyTree) : t.mirror.size = t.size := by
  induction t with
  | leaf => rfl
  | node l a r ihl ihr =>
    simp only [MyTree.mirror, MyTree.size, ihl, ihr]
    omega

example (t : MyTree) : t.mirror.mirror = t := by
  induction t with
  | leaf => rfl
  | node l a r ihl ihr =>
    simp only [MyTree.mirror, ihl, ihr]

/-! ## Part 3: Recursion that is not structural -/

def digits (n : ℕ) : ℕ :=
  if _h : n < 10 then 1 else 1 + digits (n / 10)
termination_by n
decreasing_by omega

def digitSum (n : ℕ) : ℕ :=
  if _h : n = 0 then 0 else n % 10 + digitSum (n / 10)
termination_by n
decreasing_by omega

def binLength (n : ℕ) : ℕ :=
  if _h : n = 0 then 0 else 1 + binLength (n / 2)
termination_by n
decreasing_by omega

def myGcd (m n : ℕ) : ℕ :=
  if _h : m = 0 then n else myGcd (n % m) m
termination_by m
decreasing_by exact Nat.mod_lt n (Nat.pos_of_ne_zero _h)

/-! ## Part 4: Proving things about such functions -/

example : digits 1234 = 4 := by
  simp [digits]

example (n : ℕ) (h : n < 10) : digits n = 1 := by
  rw [digits]
  simp [h]

example : digitSum 1234 = 10 := by
  simp [digitSum]

example : binLength 37 = 6 := by
  simp [binLength]

example : myGcd 48 36 = 12 := by
  simp [myGcd]

example (n : ℕ) : myGcd 0 n = n := by
  rw [myGcd]
  simp

example (n : ℕ) (h : 0 < n) :
    binLength (2 * n) = binLength n + 1 := by
  rw [binLength]
  have h1 : 2 * n ≠ 0 := by omega
  have h2 : 2 * n / 2 = n := by omega
  simp [h1, h2]
  omega

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
def two : Fin 5 := ⟨2, by decide⟩

example : two.val = 2 := rfl

-- Exercise 17) The largest element of `Fin (n + 1)`.
def myLast (n : ℕ) : Fin (n + 1) := ⟨n, by omega⟩

example (n : ℕ) : myLast n = Fin.last n := rfl

-- Exercise 18) `Fin n` sits inside `Fin (n + 1)`.
def embed {n : ℕ} (i : Fin n) : Fin (n + 1) := ⟨i.val, by omega⟩

example : (embed (2 : Fin 3)).val = 2 := rfl

-- Exercise 19) Counting from the other end: `0 ↦ n - 1`,
-- `1 ↦ n - 2`, and so on.
def rev {n : ℕ} (i : Fin n) : Fin n := ⟨n - 1 - i.val, by omega⟩

example : rev (1 : Fin 5) = 3 := by decide

-- Exercise 20) Start with `apply Fin.ext`, then `simp only [rev]`
-- and `omega`.
example {n : ℕ} (i : Fin n) : rev (rev i) = i := by
  apply Fin.ext
  simp only [rev]
  omega

/-! ## Part 6: A dependent function

`ZMod n` is ℤ/nℤ. The function `natSelf` sends `n` to the class of
`n` in ℤ/nℤ. -/

def natSelf : (n : ℕ) → ZMod n := fun n => n

-- Exercise 21) Compute `natSelf 6`, then prove it. What is
-- `natSelf n` for every `n`, and why does that not make `natSelf`
-- a constant function?
example : natSelf 6 = 0 := by
  decide
