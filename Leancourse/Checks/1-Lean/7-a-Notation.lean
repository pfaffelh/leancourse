import Mathlib

/-!
# (witness) 1.7-a -- Defining your own notation

*Notes chapter 1.7, week 9.*
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

prefix:80 "⋄" => fun n : ℕ => 2 * n
example : ⋄7 = 14 := rfl

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

/- ## Part 6: Addition before multiplication -/

section AdditionFirst

local infixl:60 " ∗ " => HMul.hMul
local infixl:60 " ÷ " => HDiv.hDiv
example : (2 : ℕ) + 3 ∗ 4 = 20 := rfl
example : (3 : ℕ) ∗ 4 + 2 = 18 := rfl
example : (8 : ℕ) - 2 ÷ 3 = 2 := rfl
example : (12 : ℕ) ÷ 2 ∗ 3 = 18 := rfl

-- 51 to 64 work. At 65 `∗` binds like `+`, and left-associativity
-- gives `3 ∗ 4 + 2 = (3 ∗ 4) + 2 = 14`. At 50 or below `∗` binds no
-- tighter than `=`, so `... = 20` is no longer parsed as intended.

example (a b c : ℚ) : a ∗ (b + c) = (a ∗ b) + (a ∗ c) := by ring

end AdditionFirst

/- ## Part 7: Notation in Mathlib -/

-- The body of `∑` is parsed at precedence 67 and stops before `+`:
-- the first sum is `(0 + 1 + 2 + 3) + 1`.
example : ∑ i ∈ Finset.range 4, i + 1 = 7 := rfl
example : ∑ i ∈ Finset.range 4, (i + 1) = 10 := rfl

example (f : ℕ → ℕ) :
    ∑ i ∈ Finset.range 5, f i = Finset.sum (Finset.range 5) f := rfl
example : {x : ℕ | x < 3} = Set.ofPred (fun x => x < 3) := rfl
example (p : ℕ → Prop) :
    (∀ᶠ n in Filter.atTop, p n) = Filter.Eventually p Filter.atTop :=
  rfl
-- The body of `∫` is parsed at precedence 60, so `+ 1` is inside.
example : ∫ x in (0 : ℝ)..1, x + 1
    = intervalIntegral (fun x => x + 1) 0 1 MeasureTheory.volume :=
  rfl

example : deriv (fun x : ℝ => x ^ 3) 2 = 12 := by
  norm_num

/- ## Part 8: `OfNat` -- where numerals come from -/

#check @OfNat.ofNat

example : (2 : ℤ) = OfNat.ofNat 2 := rfl

structure Pt where
  x : ℤ
  y : ℤ
deriving Repr, DecidableEq

instance : OfNat Pt 0 := ⟨⟨0, 0⟩⟩

example : (0 : Pt) = ⟨0, 0⟩ := rfl

#eval (0 : Pt)
