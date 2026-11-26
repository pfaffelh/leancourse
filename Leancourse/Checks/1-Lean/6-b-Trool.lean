import Mathlib

/-!
# (witness) 1.6-b -- Trool: a type with three elements

*Notes chapter 1.6, week 8.*
-/

inductive Trool where
  | no | maybe | yes
  deriving Repr, DecidableEq

namespace Trool

/- ## Part 1: Addition and multiplication -/

def add : Trool → Trool → Trool
  | no, b => b
  | a, no => a
  | maybe, maybe => yes
  | maybe, yes => no
  | yes, maybe => no
  | yes, yes => maybe

def mul : Trool → Trool → Trool
  | no, _ => no
  | _, no => no
  | maybe, b => b
  | a, maybe => a
  | yes, yes => maybe

instance : Add Trool := ⟨add⟩
instance : Mul Trool := ⟨mul⟩

instance : Zero Trool := ⟨no⟩

instance : One Trool := ⟨maybe⟩

#eval (yes + yes, yes * yes)

example : yes + yes = maybe := rfl

/- ## Part 2: Laws by cases -/

theorem add_comm' (a b : Trool) : a + b = b + a := by
  cases a <;> cases b <;> rfl

theorem add_three (a : Trool) : a + a + a = 0 := by
  cases a <;> rfl

theorem mul_add' (a b c : Trool) :
    a * (b + c) = a * b + a * c := by
  cases a <;> cases b <;> cases c <;> rfl

/- ## Part 3: An equivalence with `ZMod 3` -/

def toZMod : Trool → ZMod 3
  | no => 0
  | maybe => 1
  | yes => 2

def ofZMod (x : ZMod 3) : Trool :=
  match x with
  | 0 => no
  | 1 => maybe
  | 2 => yes

def equiv : Trool ≃ ZMod 3 where
  toFun := toZMod
  invFun := ofZMod
  left_inv := by
    intro a
    cases a <;> rfl
  right_inv := by decide

example : equiv yes = 2 := rfl

example : equiv.symm 1 = maybe := rfl

/- ## Part 4 (extra): A ring isomorphism -/

def ringEquiv : Trool ≃+* ZMod 3 where
  toEquiv := equiv
  map_add' := by
    intro a b
    cases a <;> cases b <;> rfl
  map_mul' := by
    intro a b
    cases a <;> cases b <;> rfl

example (a b c : Trool) : a * (b + c) = a * b + a * c := by
  apply ringEquiv.injective
  rw [map_mul, map_add, map_add, map_mul, map_mul, mul_add]

/-! ## Part 5: Instances are terms -/

-- Exercise 17)
-- #synth Add Trool   -- Trool.instAdd
example : (Trool.instAdd : Add Trool) = ⟨add⟩ := by
  rfl

-- Exercise 18)
example : (⟨mul⟩ : Add Trool).add yes yes = maybe := by
  rfl

/-! ## Part 6: `DecidableEq` by hand -/

-- Exercise 19)
def decEq : DecidableEq Trool
  | no, no => isTrue rfl
  | maybe, maybe => isTrue rfl
  | yes, yes => isTrue rfl
  | no, maybe => isFalse (by intro h; cases h)
  | no, yes => isFalse (by intro h; cases h)
  | maybe, no => isFalse (by intro h; cases h)
  | maybe, yes => isFalse (by intro h; cases h)
  | yes, no => isFalse (by intro h; cases h)
  | yes, maybe => isFalse (by intro h; cases h)

example : @decide (yes = maybe) (decEq yes maybe) = false := by
  rfl

-- Exercise 20)
def decEq' : DecidableEq Trool := fun a b =>
  decidable_of_iff (equiv a = equiv b) equiv.injective.eq_iff

example : @decide (yes = yes) (decEq' yes yes) = true := by
  rfl

/-! ## Part 7: Finiteness as an instance -/

-- Exercise 21) With `have`, the value of the instance is forgotten, and
-- `decide` gets stuck at `Fintype.decidableForallFintype`.
example : ∀ a b : Trool, a * b = b * a := by
  let _ : Fintype Trool := Fintype.ofEquiv (ZMod 3) equiv.symm
  decide

instance : Fintype Trool := Fintype.ofEquiv (ZMod 3) equiv.symm

-- Exercise 22)
example (a b c : Trool) : a * (b + c) = a * b + a * c := by
  revert a b c
  decide

-- Exercise 23)
example : ∀ a : Trool, a ≠ 0 → ∃ b, a * b = 1 := by
  decide

-- Exercise 24)
example : Fintype.card Trool = 3 := by
  decide

/-! ## Part 8: Following instance search -/

-- Exercise 25) From the goal down:
--   `Decidable (∀ a, a ≠ 0 → ∃ b, …)` ← `Fintype.decidableForallFintype`,
--     which needs `Fintype Trool` (our `instFintype`) and the body;
--   the implication ← `forall_prop_decidable`;
--   `a ≠ 0` ← `instDecidableNot`, then `instDecidableEqTrool`
--     (from `deriving DecidableEq`);
--   `∃ b, a * b = 1` ← `Fintype.decidableExistsFintype`, and the
--     equality again by `instDecidableEqTrool`.
-- The trace also shows the candidates that failed before each step.
-- set_option trace.Meta.synthInstance true in
#synth Decidable (∀ a : Trool, a ≠ 0 → ∃ b, a * b = 1)

-- Exercise 26) `Field (ZMod 3)` ← `ZMod.instField` ← `Fact (Nat.Prime 3)`
-- ← `Nat.fact_prime_three`, a global instance in Mathlib.
-- set_option trace.Meta.synthInstance true in
#synth Field (ZMod 3)
example : Fact (Nat.Prime 3) := Nat.fact_prime_three

end Trool
