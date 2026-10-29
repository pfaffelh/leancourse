import Mathlib

/-!
# (witness) 1.2-b -- Inductive types, pattern matching, recursion

*Notes chapter 1.2, week 4.*

Sheet `1.1-a` defined functions on `ℕ` through the recursor. Here
you declare types of your own and define functions on them by
pattern matching: one branch for each constructor. Read the sections
*Inductive types*, *Pattern matching*, *Recursion and termination*,
*Proving things about recursive definitions* and *The recursor* of
chapter 1.2 first.

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
| `T.rec`                    | the recursor of an inductive type `T`        |

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

noncomputable def MyTree.size' (t : MyTree) : ℕ :=
  MyTree.rec 0 (fun _ _ _ sl sr => sl + 1 + sr) t

example (t : MyTree) : t.size' = t.size := by
  induction t with
  | leaf => rfl
  | node l a r ihl ihr =>
    simp only [MyTree.size]
    rw [← ihl, ← ihr]
    rfl

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
