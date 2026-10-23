import Mathlib

/-!
# 1.1-a -- The recursor `Nat.rec`

*Notes chapter 1.1, week 2.*

`Nat` has two constructors, `Nat.zero` and `Nat.succ`, and one
recursor, `Nat.rec`. On this sheet every function is defined with
the recursor and every proof uses only reduction (`rfl`) and
`induction`. No lemmas from Mathlib. They come on the next sheet.

Read the sections *The natural numbers* and *Definitional equality
and `rfl`* in the chapter on the natural numbers first.

## Tactics introduced here

| tactic                 | use it when                                    |
|------------------------|------------------------------------------------|
| `show t`               | replace the goal by a definitionally equal `t` |
| `induction n with ...` | `n : ℕ` is a variable that blocks reduction    |
| `rw [h]`               | rewrite the goal with an equation `h`          |
-/

/-! ## The recursor -/

#print Nat
#check @Nat.rec

/-! To define `f : ℕ → C` you give `f 0` and a rule that computes
`f (n + 1)` from `n` and `f n`:

  Nat.rec base step 0        ⟶ base
  Nat.rec base step (n + 1)  ⟶ step n (Nat.rec base step n)

This is the ι rule. `(motive := fun _ => ℕ)` tells Lean the type of
the result; inside a `def` with a declared result type Lean finds it
on its own. -/

def myDouble (n : ℕ) : ℕ := Nat.rec 0 (fun _ j => j + 2) n

example : myDouble 2 = 4 := rfl

/-! Addition, by recursion on the *second* argument:
`myAdd m 0 = m` and `myAdd m (n + 1) = myAdd m n + 1`. -/

def myAdd (m n : ℕ) : ℕ := Nat.rec m (fun _ k => k + 1) n

example : myAdd 2 3 = 5 := rfl

-- Exercise 1) Compute the value by hand first, then prove it.
example :
    Nat.rec (motive := fun _ => ℕ) 5 (fun _ j => j + 1) 3 = 8 := by
  sorry

-- Exercise 2) Fill in the reduction of `myDouble 3` and name each
-- step (δ, β or ι). Compare with the trace in the chapter.
--
--   myDouble 3
-- ⟶ Nat.rec 0 (fun _ j => j + 2) 3   -- δ: unfold myDouble
-- ⟶ ...
-- ⟶ 6

/-! ## Defining functions with the recursor

Replace each `sorry` in a `def` by a term `Nat.rec ... ... n`. The
examples below each definition must then be provable by `rfl`. -/

-- Exercise 3) The predecessor: `myPred 0 = 0` and
-- `myPred (n + 1) = n`. The step uses `n`, not the previous value.
def myPred (n : ℕ) : ℕ := sorry

example : myPred 0 = 0 := by
  sorry

example : myPred 5 = 4 := by
  sorry

-- Exercise 4) Multiplication, using `myAdd`:
-- `myMul m 0 = 0` and `myMul m (n + 1) = myAdd (myMul m n) m`.
def myMul (m n : ℕ) : ℕ := sorry

example : myMul 3 4 = 12 := by
  sorry

-- Exercise 5) The factorial: `myFact 0 = 1` and
-- `myFact (n + 1) = (n + 1) * myFact n`.
def myFact (n : ℕ) : ℕ := sorry

example : myFact 4 = 24 := by
  sorry

-- Exercise 6) The result may have any type, here `Bool`:
-- `myEven 0 = true` and `myEven (n + 1) = !myEven n`, where
-- `!` is negation on `Bool`.
def myEven (n : ℕ) : Bool := sorry

example : myEven 4 = true := by
  sorry

example : myEven 7 = false := by
  sorry

/-! ## `rfl` or not?

`rfl` works with variables, too, as long as the recursor meets a
constructor. `myAdd m (n + 1)` reduces, because `n + 1` is
`Nat.succ n`. `myAdd m n` with a variable `n` does not. -/

-- Exercise 7) Each of the following is `rfl` or not. Decide first,
-- then prove the `rfl` ones with `rfl`. The others come back in
-- the next section.
example (m : ℕ) : myAdd m 0 = m := by
  sorry

example (m n : ℕ) : myAdd m (n + 1) = myAdd m n + 1 := by
  sorry

example (n : ℕ) : myAdd 0 n = n := by
  sorry

example (n : ℕ) : myDouble (n + 1) = myDouble n + 2 := by
  sorry

example (n : ℕ) : myEven (n + 2) = myEven n := by
  sorry

/-! ## Induction

When the recursor is stuck on a variable `n`, apply it yourself.
`induction n` is `Nat.rec` for proofs: one goal for `0`, one for
`k + 1`, and in the second the *induction hypothesis* `ih` for `k`.
In each goal the recursor meets a constructor and reduces again.
`show` makes the reduced form visible, so that `rw [ih]` finds its
pattern. -/

theorem myAdd_zero_left (n : ℕ) : myAdd 0 n = n := by
  induction n with
  | zero => rfl
  | succ k ih =>
      show myAdd 0 k + 1 = k + 1
      rw [ih]

-- Exercise 8) Recursion on the second argument, so induction on `n`.
theorem myAdd_succ_left (m n : ℕ) :
    myAdd (m + 1) n = myAdd m n + 1 := by
  sorry

-- Exercise 9) Commutativity. Use the two theorems above.
theorem myAdd_comm (m n : ℕ) : myAdd m n = myAdd n m := by
  sorry

-- Exercise 10) Use `myAdd_succ_left`. After `rw`, the goal may be
-- closed by `rfl`.
example (n : ℕ) : myDouble n = myAdd n n := by
  sorry

-- Exercise 11) `!!b = b` is not `rfl` for a variable `b`: `!` has
-- to see `true` or `false`. After `show`, `cases (myEven n)` puts in
-- `false` and `true` in turn, and `<;> rfl` closes both goals.
-- (`cases` is the subject of the next sheet.)
example (n : ℕ) : myEven (n + 2) = myEven n := by
  sorry

/-! ## Associativity by reduction

Lean's own `+` on `ℕ` is also defined by recursion on the second
argument. The chapter proves `0 + n = n` by induction, using
`Nat.add_succ`. -/

-- Exercise 12) Here associativity is just reduction: both sides
-- reduce to `Nat.succ (m + k)`.
example (m k : ℕ) : m + (k + 1) = (m + k) + 1 := by
  sorry

-- Exercise 13) Prove `0 + n = n` as in the chapter, but without
-- `Nat.add_succ`: use `show` and Exercise 12.
example (n : ℕ) : 0 + n = n := by
  sorry
