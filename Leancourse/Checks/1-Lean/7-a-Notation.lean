import Mathlib

/-!
# (witness) 1.7-a -- Defining your own notation

*Notes chapter 1.7, week 8.*
-/

/- ## Part 1: Simple `notation` -/

notation "π₂" => (2 : ℕ)
example : π₂ = 2 := rfl

notation "sq " x => x * x
example : (sq 5 : ℕ) = 25 := rfl

notation "avg(" a ", " b ")" => (a + b) / 2
example : (avg(4, 6) : ℕ) = 5 := rfl

/- ## Part 2: Infix operators -/

infixl:65 " ⊙ " => fun (a b : ℕ) => a + 2 * b
example : (1 ⊙ 2 : ℕ) = 5 := rfl
example : (1 ⊙ 2 ⊙ 3 : ℕ) = 11 := rfl

infixr:65 " ▷ " => fun (a b : ℕ) => a + 2 * b
example : (1 ▷ 2 ▷ 3 : ℕ) = 17 := rfl

/- ## Part 3: `prefix` and `postfix` -/

prefix:80 "‼" => fun n : ℕ => 2 * n
example : ‼7 = 14 := rfl

postfix:90 "⁺⁺" => fun n : ℕ => n + 1
example : (3 : ℕ)⁺⁺ = 4 := rfl

/- ## Part 4: `scoped` notation -/

namespace MyArith
  scoped notation "↯" => (100 : ℕ)
end MyArith

open scoped MyArith
example : ↯ = 100 := rfl

/- ## Part 5: Mixing notation -/

notation "‖" x "‖₁" => Int.natAbs x
example : ‖(-3 : ℤ)‖₁ = 3 := rfl
example (n : ℤ) : 0 ≤ (‖n‖₁ : ℤ) := by positivity

notation "if! " c " then! " a " else! " b => bif c then a else b
example : (if! true  then! 1 else! 2 : ℕ) = 1 := rfl
example : (if! false then! 1 else! 2 : ℕ) = 2 := rfl
