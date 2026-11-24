import Mathlib

/-!
# 1.6-d -- Trool: a type with three elements

*Notes chapter 1.6, week 8.*

`Bool` has two elements, `Trool` has three. You give it an addition
and a multiplication, check the laws by going through all cases, and
then show that `Trool` is `ZMod 3` with other names: there is an
equivalence `Trool ≃ ZMod 3`, and in the extra part a ring
isomorphism.

The names `no`, `maybe`, `yes` are labels. What `+` and `*` mean is
decided by the instances you write, not by the names. Chapter 1.6
builds the same type under the name `Mod3`, section *Defining
multiple instances*.

## Introduced here

| notation        | what it does                                      |
|-----------------|---------------------------------------------------|
| `α ≃ β`         | an equivalence: maps both ways, inverse to each other |
| `e x`, `e.symm y` | apply an equivalence, or its inverse            |
| `α ≃+* β`       | a ring isomorphism: an equivalence with `+`, `*`  |
| `e.injective`   | an equivalence is injective                       |
| `map_add`, `map_mul` | a ring isomorphism respects `+` and `*`      |

## Tactics from earlier sheets

| sheet   | tactics                        |
|---------|--------------------------------|
| `L-a`   | `intro`, `apply`               |
| `1.1-a` | `rfl`, `rw`                    |
| `1.1-b` | `cases`, `<;>`, `decide`       |
-/

inductive Trool where
  | no | maybe | yes
  deriving Repr, DecidableEq

namespace Trool

/-! ## Part 1: Addition and multiplication

Read `no` as `0`, `maybe` as `1` and `yes` as `2`, and compute
modulo `3`. The addition table:

| `+`     | `no`    | `maybe` | `yes`   |
|---------|---------|---------|---------|
| `no`    | `no`    | `maybe` | `yes`   |
| `maybe` | `maybe` | `yes`   | `no`    |
| `yes`   | `yes`   | `no`    | `maybe` |
-/

-- Exercise 1) Define the addition by pattern matching. The first two
-- cases are given; four are left.
def add : Trool → Trool → Trool
  | no, b => b
  | a, no => a
  | _, _ => sorry

-- Exercise 2) Define the multiplication, again modulo `3`.
def mul : Trool → Trool → Trool :=
  sorry

instance : Add Trool := ⟨add⟩
instance : Mul Trool := ⟨mul⟩

-- Exercise 3) Make `no` the zero of `Trool`.
instance : Zero Trool :=
  sorry

-- Exercise 4) Make `maybe` the one of `Trool`.
instance : One Trool :=
  sorry

-- #eval (yes + yes, yes * yes)   -- (Trool.maybe, Trool.maybe)

-- Exercise 5) Two plus two is four, which is one.
example : yes + yes = maybe := by
  sorry

/-! ## Part 2: Laws by cases

`Trool` has three elements, so a law in two variables has nine cases
and a law in three variables has 27. `cases a <;> cases b <;> rfl`
goes through all of them. -/

-- Exercise 6)
theorem add_comm' (a b : Trool) : a + b = b + a := by
  sorry

-- Exercise 7) Three times anything is zero.
theorem add_three (a : Trool) : a + a + a = 0 := by
  sorry

-- Exercise 8) The distributive law, 27 cases.
theorem mul_add' (a b c : Trool) :
    a * (b + c) = a * b + a * c := by
  sorry

/-! ## Part 3: An equivalence with `ZMod 3`

An equivalence `α ≃ β` is a structure with four fields:

```
structure Equiv (α β : Sort*) where
  toFun : α → β
  invFun : β → α
  left_inv : ∀ a, invFun (toFun a) = a
  right_inv : ∀ b, toFun (invFun b) = b
```

(`left_inv` and `right_inv` are stated in Mathlib with
`Function.LeftInverse`, which unfolds to the `∀` above.) An
equivalence `e` is applied like a function, `e a`; its inverse is
`e.symm`. -/

-- Exercise 9) The map to `ZMod 3`.
def toZMod : Trool → ZMod 3 :=
  sorry

-- Exercise 10) The map back. `ZMod 3` is `Fin 3`, so you may match
-- on the numerals `0`, `1`, `2`, and Lean sees that the cases are
-- complete.
def ofZMod (x : ZMod 3) : Trool :=
  sorry

-- Exercise 11) Put them together. For `left_inv` go through the
-- three elements of `Trool`; `right_inv` is a statement about all
-- three elements of `ZMod 3`, and `decide` checks it.
def equiv : Trool ≃ ZMod 3 where
  toFun := toZMod
  invFun := ofZMod
  left_inv := sorry
  right_inv := sorry

-- Exercise 12)
example : equiv yes = 2 := by
  sorry

-- Exercise 13)
example : equiv.symm 1 = maybe := by
  sorry

/-! ## Part 4 (extra): A ring isomorphism

`Trool ≃+* ZMod 3` is an equivalence that also respects `+` and `*`.
It extends `Trool ≃ ZMod 3` by two fields, `map_add'` and
`map_mul'`. -/

-- Exercise 14) Nine cases each.
def ringEquiv : Trool ≃+* ZMod 3 where
  toEquiv := equiv
  map_add' := sorry
  map_mul' := sorry

-- Exercise 15) Exercise 8 again, without the 27 cases. Apply
-- `ringEquiv.injective`: the goal becomes an equation in `ZMod 3`.
-- Move `ringEquiv` inwards with `map_add` and `map_mul`, and finish
-- with the distributive law of `ZMod 3`, `mul_add`.
example (a b c : Trool) : a * (b + c) = a * b + a * c := by
  sorry

-- Exercise 16) Which of the two proofs of the distributive law still
-- works for a type with 100 elements? Answer in a comment.

end Trool
