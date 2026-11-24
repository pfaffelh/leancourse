import Mathlib

/-!
# (witness) 1.6-d -- Trool: a type with three elements

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

end Trool
