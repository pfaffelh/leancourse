import Mathlib

/-!
# 1.6-b -- Trool: a type with three elements

*Notes chapter 1.6, week 8.*

`Bool` has two elements, `Trool` has three. You give it an addition
and a multiplication, check the laws by going through all cases, and
then show that `Trool` is `ZMod 3` with other names: there is an
equivalence `Trool ≃ ZMod 3`, and in the extra part a ring
isomorphism. Parts 5 to 8 redo the typeclass material of chapter 1.6
on `Trool`: instances as terms, `DecidableEq` by hand, a local and a
global `Fintype` instance, and the chain that instance search builds.

The names `no`, `maybe`, `yes` are labels. What `+` and `*` mean is
decided by the instances you write, not by the names.

## Introduced here

| notation        | what it does                                      |
|-----------------|---------------------------------------------------|
| `α ≃ β`         | an equivalence: maps both ways, inverse to each other |
| `e x`, `e.symm y` | apply an equivalence, or its inverse            |
| `α ≃+* β`       | a ring isomorphism: an equivalence with `+`, `*`  |
| `e.injective`   | an equivalence is injective                       |
| `map_add`, `map_mul` | a ring isomorphism respects `+` and `*`      |
| `#synth C`      | the instance that instance search finds for `C`   |
| `decidable_of_iff` | a `Decidable` instance along an `↔`            |
| `Fintype α`     | a finite list of all elements of `α`              |
| `Fintype.ofEquiv` | transport `Fintype` along an equivalence        |

## Tactics from earlier sheets

| sheet   | tactics                        |
|---------|--------------------------------|
| `L-a`   | `intro`, `apply`, `revert`     |
| `1.1-a` | `rfl`, `rw`                    |
| `1.1-b` | `cases`, `<;>`, `decide`       |
| `1.6-a` | `let`                          |
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

/-! ## Part 5: Instances are terms

`Add Trool` is a structure type with one field `add : Trool → Trool →
Trool`. Every binary operation on `Trool` gives an element of it. The
instance above is the one that is registered, so `+` uses it.
Chapter 1.6, *Data classes and Prop classes*. -/

-- Exercise 17) Find the name of the registered instance with
-- `#synth Add Trool`, then replace `sorry` by that name. `rfl` proves
-- that it is the structure value `⟨add⟩`.
-- #synth Add Trool
example : (sorry : Add Trool) = ⟨add⟩ := by
  sorry

-- Exercise 18) `⟨mul⟩` is another element of `Add Trool`. It is not
-- registered, so `+` never uses it. Compute its `add` by hand.
example : (⟨mul⟩ : Add Trool).add yes yes = sorry := by
  sorry

/-! ## Part 6: `DecidableEq` by hand

`deriving DecidableEq` in the declaration of `Trool` generated an
instance of `DecidableEq Trool = (a b : Trool) → Decidable (a = b)`.
Here you write it yourself, twice. For a test, the instance is given
explicitly, with `@decide _ (d a b)`. -/

-- Exercise 19) Nine cases. Equal constructors: `isTrue rfl`. Different
-- constructors: `isFalse h` with `h : a ≠ b`; `by intro h; cases h`
-- proves it.
def decEq : DecidableEq Trool :=
  sorry

example : @decide (yes = maybe) (decEq yes maybe) = false := by
  sorry -- rfl, once solved

-- Exercise 20) Without cases: `equiv` from Part 3 is injective, so
-- `a = b` holds exactly when `equiv a = equiv b`, which is decidable in
-- `ZMod 3`. Use `decidable_of_iff` and `equiv.injective.eq_iff`.
def decEq' : DecidableEq Trool := fun a b =>
  sorry

example : @decide (yes = yes) (decEq' yes yes) = true := by
  sorry -- rfl, once solved

/-! ## Part 7: Finiteness as an instance

`decide` proves a statement `∀ a : Trool, …` if it finds an instance of
`Fintype Trool`: a finite list of all elements. `Fintype.ofEquiv`
transports the one of `ZMod 3` along `equiv.symm`. Chapter 1.6,
*Local instances: `have` or `let`*. -/

-- Exercise 21) Supply the instance inside the proof:
-- `have _ : Fintype Trool := Fintype.ofEquiv (ZMod 3) equiv.symm`, then
-- `decide`. Read the error. Then replace `have` by `let`.
example : ∀ a b : Trool, a * b = b * a := by
  sorry

-- From here on, the instance is global.
instance : Fintype Trool := Fintype.ofEquiv (ZMod 3) equiv.symm

-- Exercise 22) Compare with Exercise 8: one tactic, no `cases`.
-- Hint: `revert a b c` first.
example (a b c : Trool) : a * (b + c) = a * b + a * c := by
  sorry

-- Exercise 23) Every element other than `0` has an inverse.
example : ∀ a : Trool, a ≠ 0 → ∃ b, a * b = 1 := by
  sorry

-- Exercise 24)
example : Fintype.card Trool = 3 := by
  sorry

/-! ## Part 8: Following instance search

`set_option trace.Meta.synthInstance true in` before a command shows
how instance search works: it starts at the goal, applies an instance,
and continues with that instance's hypotheses. Chapter 1.6,
*Propositions as instances: `Fact`*. -/

-- Exercise 25) Which instances does `decide` use in Exercise 23? Run
-- the trace and write the chain in a comment: which instance gives the
-- `Decidable (∀ …)`, which one `Fintype Trool`, which one the equality
-- `a * b = 1`?
-- set_option trace.Meta.synthInstance true in
-- #synth Decidable (∀ a : Trool, a ≠ 0 → ∃ b, a * b = 1)

-- Exercise 26) `ZMod 3` is a field. `ZMod.instField` needs
-- `[Fact (Nat.Prime 3)]`, and nobody wrote a `have`. Which instance
-- supplies it? Find out with the trace, and replace `sorry` by its
-- name.
-- set_option trace.Meta.synthInstance true in
-- #synth Field (ZMod 3)
example : Fact (Nat.Prime 3) := sorry

end Trool
