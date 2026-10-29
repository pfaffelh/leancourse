import Mathlib

/-!
# (witness) 1.2-c -- Structures and `Fin`

*Notes chapter 1.2, week 5.*

A structure is an inductive type with one constructor and named
fields. Here you build structures with a proof among their fields,
define operations on them, extend them, and work with `Fin n`, the
structure of a number together with a proof that it is less than
`n`. Read *Structures* in chapter 1.2 first.

## Introduced here

| notation / tactic          | use it when                                   |
|----------------------------|-----------------------------------------------|
| `structure S where`        | declare a type with named fields              |
| `⟨a, b, h⟩`, `where`       | build a value of a structure                  |
| `{ s with x := a }`        | copy `s`, changing the field `x`              |
| `s.f` for `S.f s`          | an operation on `S`, called with a dot        |
| `structure T extends S`    | add fields to the structure `S`               |
| `cases h` on `h : a = b`   | replace `b` by `a` everywhere                 |
| `⟨i, h⟩ : Fin n`           | build an element from `i` and `h : i < n`     |
| `Fin.ext`                  | prove `a = b` from `a.val = b.val`            |

`decide` is known from `1.1-b`, `omega` from `1.1-c`.
-/

/-! ## Part 1: Structures -/

structure NatInterval where
  lo : ℕ
  hi : ℕ
  le : lo ≤ hi

def zeroOne : NatInterval := ⟨0, 1, by omega⟩

def NatInterval.length (I : NatInterval) : ℕ := I.hi - I.lo

example : zeroOne.length = 1 := rfl

def NatInterval.shift (I : NatInterval) (k : ℕ) : NatInterval where
  lo := I.lo + k
  hi := I.hi + k
  le := by have := I.le; omega

example (I : NatInterval) (k : ℕ) :
    (I.shift k).length = I.length := by
  simp only [NatInterval.shift, NatInterval.length]
  omega

def NatInterval.hull (I J : NatInterval) : NatInterval where
  lo := min I.lo J.lo
  hi := max I.hi J.hi
  le := by have := I.le; omega

example : { zeroOne with hi := 5, le := by decide }.length = 5 :=
  rfl

example (I J : NatInterval) (h1 : I.lo = J.lo) (h2 : I.hi = J.hi) :
    I = J := by
  cases I
  cases J
  cases h1
  cases h2
  rfl

/-! An operation on a structure is an ordinary function. If its name
begins with the name of the type, it can be called with a dot. -/

def NatInterval.Contains (I : NatInterval) (n : ℕ) : Prop :=
  I.lo ≤ n ∧ n ≤ I.hi

example (I : NatInterval) : I.Contains I.lo := by
  have := I.le
  constructor <;> omega

/-! `extends` adds fields to an existing structure. An interval with
a marked point in it: -/

structure PointedInterval extends NatInterval where
  pt : ℕ
  lo_le : lo ≤ pt
  le_hi : pt ≤ hi

def mid : PointedInterval :=
  { lo := 0, hi := 4, le := by decide,
    pt := 2, lo_le := by decide, le_hi := by decide }

example : mid.length = 4 := by
  rfl

example (I : PointedInterval) : I.Contains I.pt := by
  exact ⟨I.lo_le, I.le_hi⟩

/-! ## Part 2: `Fin n`, a structure with a proof

An element of `Fin n` is a pair `⟨i, h⟩` of a number `i : ℕ` and a
proof `h : i < n`. The fields are `val` and `isLt`. Two elements are
equal when their values are: `Fin.ext : a.val = b.val → a = b`.
`omega` knows that `i.val < n` for `i : Fin n`. Read *Data with a
property* in chapter 1.2.

Fill in each definition. The `example` below it should then be
provable by `rfl` (by `decide` for Exercise 11). -/

example : Fin 3 := ⟨2, by decide⟩

-- Exercise 1)
def two : Fin 5 := ⟨2, by decide⟩

example : two.val = 2 := rfl

-- Exercise 2) The largest element of `Fin (n + 1)`.
def myLast (n : ℕ) : Fin (n + 1) := ⟨n, by omega⟩

example (n : ℕ) : myLast n = Fin.last n := rfl

-- Exercise 3) `Fin n` sits inside `Fin (n + 1)`.
def embed {n : ℕ} (i : Fin n) : Fin (n + 1) := ⟨i.val, by omega⟩

example : (embed (2 : Fin 3)).val = 2 := rfl

-- Exercise 4) Counting from the other end: `0 ↦ n - 1`,
-- `1 ↦ n - 2`, and so on.
def rev {n : ℕ} (i : Fin n) : Fin n := ⟨n - 1 - i.val, by omega⟩

example : rev (1 : Fin 5) = 3 := by decide

-- Exercise 5) Start with `apply Fin.ext`, then `simp only [rev]`
-- and `omega`.
example {n : ℕ} (i : Fin n) : rev (rev i) = i := by
  apply Fin.ext
  simp only [rev]
  omega

/-! ## Part 3: A dependent function

`ZMod n` is ℤ/nℤ. The function `natSelf` sends `n` to the class of
`n` in ℤ/nℤ. -/

def natSelf : (n : ℕ) → ZMod n := fun n => n

-- Exercise 6) Compute `natSelf 6`, then prove it. What is
-- `natSelf n` for every `n`, and why does that not make `natSelf`
-- a constant function?
example : natSelf 6 = 0 := by
  decide
