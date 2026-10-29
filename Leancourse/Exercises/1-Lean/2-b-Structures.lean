import Mathlib

/-!
# 1.2-b -- Structures and `Fin`

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

/-! ## Part 1: Structures

An interval of natural numbers: two numbers and a proof that the
first is at most the second. (`Interval` is taken in Mathlib.) -/

structure NatInterval where
  lo : ℕ
  hi : ℕ
  le : lo ≤ hi

def zeroOne : NatInterval := ⟨0, 1, by omega⟩

def NatInterval.length (I : NatInterval) : ℕ := I.hi - I.lo

example : zeroOne.length = 1 := rfl

/-! `with` copies a value and changes some fields. When `hi`
changes, the proof `le` has to be given again. -/

example : { zeroOne with hi := 5, le := by decide }.length = 5 :=
  rfl

-- Exercise 1) Shift an interval by `k`. For `le`, `have := I.le`
-- puts the old proof into the context, and then `omega` finishes.
def NatInterval.shift (I : NatInterval) (k : ℕ) : NatInterval where
  lo := I.lo + k
  hi := I.hi + k
  le := sorry

-- Exercise 2) Unfold with `simp only [NatInterval.shift,
-- NatInterval.length]`, then `omega`.
example (I : NatInterval) (k : ℕ) :
    (I.shift k).length = I.length := by
  sorry

-- Exercise 3) The smallest interval containing `I` and `J`. `omega`
-- knows `min` and `max`.
def NatInterval.hull (I J : NatInterval) : NatInterval where
  lo := sorry
  hi := sorry
  le := sorry

-- Exercise 4) Two intervals with the same ends are equal: the
-- proofs `le` are equal anyway. `cases I` and `cases J` expose the
-- fields; `cases h1` then replaces one end by the other. Then
-- `rfl`.
example (I J : NatInterval) (h1 : I.lo = J.lo) (h2 : I.hi = J.hi) :
    I = J := by
  sorry

/-! An operation on a structure is an ordinary function. If its name
begins with the name of the type, it can be called with a dot. -/

def NatInterval.Contains (I : NatInterval) (n : ℕ) : Prop :=
  I.lo ≤ n ∧ n ≤ I.hi

-- Exercise 5) `I.Contains I.lo` is `NatInterval.Contains I I.lo`.
-- `have := I.le`, then `constructor <;> omega`.
example (I : NatInterval) : I.Contains I.lo := by
  sorry

/-! `extends` adds fields to an existing structure. An interval with
a marked point in it: -/

structure PointedInterval extends NatInterval where
  pt : ℕ
  lo_le : lo ≤ pt
  le_hi : pt ≤ hi

-- Exercise 6) The interval from `0` to `4` with the point `2`. Give
-- all six fields, inherited and new; the proofs by `decide`.
def mid : PointedInterval :=sorry

-- `length` is inherited from `NatInterval`. This should be `rfl`.
example : mid.length = 4 := by
  sorry

-- Exercise 7) `Contains` is inherited as well. A term suffices.
example (I : PointedInterval) : I.Contains I.pt := by
  sorry

/-! ## Part 2: `Fin n`, a structure with a proof

An element of `Fin n` is a pair `⟨i, h⟩` of a number `i : ℕ` and a
proof `h : i < n`. The fields are `val` and `isLt`. Two elements are
equal when their values are: `Fin.ext : a.val = b.val → a = b`.
`omega` knows that `i.val < n` for `i : Fin n`. Read *Data with a
property* in chapter 1.2.

Fill in each definition. The `example` below it should then be
provable by `rfl` (by `decide` for Exercise 11). -/

example : Fin 3 := ⟨2, by decide⟩

-- Exercise 8)
def two : Fin 5 := sorry

example : two.val = 2 := by
  sorry

-- Exercise 9) The largest element of `Fin (n + 1)`.
def myLast (n : ℕ) : Fin (n + 1) := sorry

example (n : ℕ) : myLast n = Fin.last n := by
  sorry

-- Exercise 10) `Fin n` sits inside `Fin (n + 1)`.
def embed {n : ℕ} (i : Fin n) : Fin (n + 1) := sorry

example : (embed (2 : Fin 3)).val = 2 := by
  sorry

-- Exercise 11) Counting from the other end: `0 ↦ n - 1`,
-- `1 ↦ n - 2`, and so on.
def rev {n : ℕ} (i : Fin n) : Fin n := sorry

example : rev (1 : Fin 5) = 3 := by
  sorry

-- Exercise 12) Start with `apply Fin.ext`, then `simp only [rev]`
-- and `omega`.
example {n : ℕ} (i : Fin n) : rev (rev i) = i := by
  sorry

/-! ## Part 3: A dependent function

`ZMod n` is ℤ/nℤ. The function `natSelf` sends `n` to the class of
`n` in ℤ/nℤ. -/

def natSelf : (n : ℕ) → ZMod n := fun n => n

-- Exercise 13) Compute `natSelf 6`, then prove it. What is
-- `natSelf n` for every `n`, and why does that not make `natSelf`
-- a constant function?
example : natSelf 6 = 0 := by
  sorry
