import Mathlib

/-!
# (witness) 1.1-b -- `Bool`

*Notes chapter 1.1, week 3.*

`Bool` is the smallest interesting inductive type: two constructors,
no arguments. Reduction, `rfl` and stuck terms work as for `Nat` on
the previous sheet, but without induction. New is case analysis
with `cases`.

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
  rfl

/-! `!`, `&&` and `||` are ordinary functions on `Bool`, defined by
matching on the *first* argument. On constructors they compute. -/

example : (true && !false) = true := rfl

-- Exercise 2)
example : (false || (true && true)) = true := by
  rfl

/-! ## `decide`

`decide` evaluates a statement that contains no variables and closes
the goal if the value is `true`. It also works for `≠`. -/

example : (2 : ℕ) + 2 ≠ 5 := by
  decide

-- Exercise 3) The two constructors are different.
example : true ≠ false := by
  decide

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
  rfl

example (b : Bool) : (b || true) = true := by
  cases b <;> rfl

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
  cases b <;> rfl

-- Exercise 6)
example (b : Bool) : (!!b) = b := by
  cases b <;> rfl

-- Exercise 7) Two variables, so two `cases`. Four goals in total.
example (a b : Bool) : (a && b) = (b && a) := by
  cases a <;> cases b <;> rfl

-- Exercise 8) De Morgan for `Bool`.
example (a b : Bool) : (!(a && b)) = (!a || !b) := by
  cases a <;> cases b <;> rfl

-- Exercise 9)
example (a b c : Bool) :
    (a && (b || c)) = ((a && b) || (a && c)) := by
  cases a <;> cases b <;> cases c <;> rfl

/-! ## Defining functions on `Bool`

There are two ways: with the recursor, or with `match`. They are
definitionally equal on constructors. -/

def myNot (b : Bool) : Bool := Bool.rec true false b

def myNot' : Bool → Bool
  | false => true
  | true  => false

-- Exercise 10) Show that both agree with `!`.
example (b : Bool) : myNot b = !b := by
  cases b <;> rfl

example (b : Bool) : myNot' b = !b := by
  cases b <;> rfl

-- Exercise 11) Define exclusive or with `match` on both arguments,
-- then prove it is commutative and that `myXor b b = false`.
def myXor : Bool → Bool → Bool
  | false, b => b
  | true,  b => !b

example (a b : Bool) : myXor a b = myXor b a := by
  cases a <;> cases b <;> rfl

example (b : Bool) : myXor b b = false := by
  cases b <;> rfl

/-! ## `bif`

`bif b then x else y` is `cond b x y`, again defined by matching on
`b`. -/

-- Exercise 12)
example {α : Type} (b : Bool) (x : α) :
    (bif b then x else x) = x := by
  cases b <;> rfl

-- Exercise 13)
example {α : Type} (b : Bool) (x y : α) :
    (bif !b then x else y) = (bif b then y else x) := by
  cases b <;> rfl

/-! ## `Bool` and `Prop`

A `Bool` is a value. A statement is a `Prop`. The bridge is the
proposition `b = true`. Lean inserts it silently when a `Bool` stands
where a `Prop` is expected. -/

-- Exercise 14) Every `Bool` is one of the two constructors.
example (b : Bool) : b = true ∨ b = false := by
  cases b
  · right; rfl
  · left; rfl

-- Exercise 15) `cases a <;> cases b <;> decide` works here. Why does
-- `decide` alone, without the `cases`, not work?
example (a b : Bool) :
    (a && b) = true ↔ a = true ∧ b = true := by
  cases a <;> cases b <;> decide

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
  cases b <;> cases h1 : f true <;> cases h2 : f false <;>
    simp [h1, h2]

-- Exercise 17)
example (h : False) : 0 = 1 :=
  False.rec (fun _ => 0 = 1) h

-- Exercise 18)
example (P : Prop) (h : False) : P := by
  exfalso
  exact h

example (P : Prop) (h : False) : P := by
  exact False.elim h

example (P : Prop) (h : False) : P := by
  cases h

-- Exercise 19)
example (P : Prop) (hP : P) (h : True) : P := by
  cases h
  exact hP

-- Exercise 20)
example (h : true = false) : False := by
  cases h

-- Exercise 21)
example (P : Prop) (h : 0 = 1) : P := by
  cases h

-- Exercise 22)
def fromEmpty : Empty → ℕ := Empty.elim
