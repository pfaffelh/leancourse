import Mathlib

/-!
# 02-00 -- `Bool`

`Bool` is the smallest interesting inductive type: two constructors,
no arguments. Everything that `Nat` does with reduction, `rfl` and
case analysis already happens here, without the induction.

Read the section *Bool* in the chapter on the natural numbers first.

## Tactics introduced here

| tactic       | use it when                                        |
|--------------|----------------------------------------------------|
| `rfl`        | both sides reduce to the same term                 |
| `decide`     | the statement has no variables and can be computed |
| `cases b`    | `b : Bool` is a variable that blocks reduction     |
| `t <;> s`    | run `s` on every goal that `t` produces            |
| `cases h : e`| split on the value of an expression `e`            |
-/

/-! ## Constructors and the recursor -/

#print Bool
#check @Bool.rec

/-! `Bool.rec e f b` is "if `b` then `f` else `e`". The `false` case
comes first. Applied to a constructor it reduces (ι rule), so `rfl`
proves the result. -/

example : Bool.rec 1 2 false = (1 : ℕ) := rfl

-- Exercise 1) Why `"yes"`? Then prove it.
example : Bool.rec "no" "yes" true = "yes" := by
  sorry

/-! `!`, `&&` and `||` are ordinary functions on `Bool`, defined by
matching on the *first* argument. On constructors they compute. -/

example : (true && !false) = true := rfl

-- Exercise 2)
example : (false || (true && true)) = true := by
  sorry

/-! ## `decide`

`decide` evaluates a statement that contains no variables and closes
the goal if the value is `true`. It also works for `≠`. -/

example : (2 : ℕ) + 2 ≠ 5 := by
  decide

-- Exercise 3) The two constructors are different.
example : true ≠ false := by
  sorry

/-! ## When reduction gets stuck

`||` matches on its first argument:

  true  || y  ⟶ true
  false || y  ⟶ y

So `true || b` reduces, although `b` is unknown. `b || true` does
not: Lean cannot pick a branch without knowing `b`. This is the same
effect as `0 + n` versus `n + 0` for `Nat`. -/

-- Exercise 4) One of these is `rfl`, the other is not. Which one,
-- and why? Prove the `rfl` one with `rfl`; leave the other for
-- Exercise 5.
example (b : Bool) : (true || b) = true := by
  sorry

example (b : Bool) : (b || true) = true := by
  sorry

/-! ## `cases`

`cases b` replaces the variable `b` by each constructor in turn. You
get two goals, one with `false` and one with `true`. In each, the
term reduces again. -/

example (b : Bool) : (b && false) = false := by
  cases b
  · rfl
  · rfl

/-! The two goals are proved the same way. `cases b <;> rfl` runs
`rfl` on both. -/

example (b : Bool) : (b && false) = false := by
  cases b <;> rfl

-- Exercise 5) Now the second statement of Exercise 4.
example (b : Bool) : (b || true) = true := by
  sorry

-- Exercise 6)
example (b : Bool) : (!!b) = b := by
  sorry

-- Exercise 7) Two variables, so two `cases`. Four goals in total.
example (a b : Bool) : (a && b) = (b && a) := by
  sorry

-- Exercise 8) De Morgan for `Bool`.
example (a b : Bool) : (!(a && b)) = (!a || !b) := by
  sorry

-- Exercise 9)
example (a b c : Bool) :
    (a && (b || c)) = ((a && b) || (a && c)) := by
  sorry

/-! ## Defining functions on `Bool`

There are two ways: with the recursor, or with `match`. They are
definitionally equal on constructors. -/

def myNot (b : Bool) : Bool := Bool.rec true false b

def myNot' : Bool → Bool
  | false => true
  | true  => false

-- Exercise 10) Show that both agree with `!`.
example (b : Bool) : myNot b = !b := by
  sorry

example (b : Bool) : myNot' b = !b := by
  sorry

-- Exercise 11) Define exclusive or with `match` on both arguments,
-- then prove it is commutative and that `myXor b b = false`.
def myXor : Bool → Bool → Bool
  | _, _ => sorry

example (a b : Bool) : myXor a b = myXor b a := by
  sorry

example (b : Bool) : myXor b b = false := by
  sorry

/-! ## `bif`

`bif b then x else y` is `cond b x y`, again defined by matching on
`b`. -/

-- Exercise 12)
example {α : Type} (b : Bool) (x : α) :
    (bif b then x else x) = x := by
  sorry

-- Exercise 13)
example {α : Type} (b : Bool) (x y : α) :
    (bif !b then x else y) = (bif b then y else x) := by
  sorry

/-! ## `Bool` and `Prop`

A `Bool` is a value. A statement is a `Prop`. The bridge is the
proposition `b = true`. Lean inserts it silently when a `Bool` stands
where a `Prop` is expected. -/

-- Exercise 14) Every `Bool` is one of the two constructors.
example (b : Bool) : b = true ∨ b = false := by
  sorry

-- Exercise 15) `cases a <;> cases b <;> decide` works here. Why does
-- `decide` alone, without the `cases`, not work?
example (a b : Bool) :
    (a && b) = true ↔ a = true ∧ b = true := by
  sorry

/-! ## Splitting on an expression

`cases b` needs a variable. To split on the value of an expression
`e`, write `cases h : e`. It replaces `e` by each constructor and
records which one in the hypothesis `h`. -/

example (f : Bool → Bool) : f true = true ∨ f true = false := by
  cases h : f true
  · right; rfl
  · left; rfl

-- Exercise 16) There are only four functions `Bool → Bool`. Hence
-- applying one three times is the same as applying it once. Split on
-- `b`, on `f true` and on `f false`; then `simp [h1, h2]` closes all
-- eight goals.
example (f : Bool → Bool) (b : Bool) : f (f (f b)) = f b := by
  sorry
