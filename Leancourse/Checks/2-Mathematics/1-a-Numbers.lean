import Mathlib

/-!
# (witness) 2.1-a -- Numbers

*Notes chapter 2.1, week 9.* Exercises 1, 2, 5, 8 and 11 change the
statement as the sheet asks.
-/

open scoped NNReal ENNReal

-- Exercise 1)
example : Int.negSucc 0 = -1 := by
  rfl

-- Exercise 2)
example : (10 / 4 : ℚ).num = 5 ∧ (10 / 4 : ℚ).den = 2 := by
  constructor <;> norm_num

-- Exercise 3)
example (x : ℝ≥0) : 0 ≤ (x : ℝ) := by
  exact x.2

-- Exercise 4)
example (z : ℂ) : z = ⟨z.re, z.im⟩ := by
  rfl

-- Exercise 5)
example : (3 : ℕ) - 5 + 5 = 5 := by
  decide

-- Exercise 6)
example (n m : ℕ) (h : m ≤ n) : n - m + m = n := by
  omega

-- Exercise 7)
example : ¬ ∀ n m : ℕ, n - m + m = n := by
  intro h
  have := h 0 1
  omega

-- Exercise 8)
example : (-9 : ℤ) / 4 = -3 ∧ (-9 : ℤ) % 4 = 3 := by
  decide

-- Exercise 9)
example (x : ℝ) : x / 0 = 0 := by
  simp

-- Exercise 10)
example : Real.sqrt (-4) = 0 := by
  exact Real.sqrt_eq_zero_of_nonpos (by norm_num)

-- Exercise 11)
example (a b : ℝ) (h : b ≠ 0) : a / b * b = a := by
  exact div_mul_cancel₀ a h

-- Exercise 12) For `c = 0` both sides are `0`.
example (a b c : ℝ) : (a + b) / c = a / c + b / c := by
  exact add_div a b c

-- Exercise 13) `1 / 2` is read in `ℕ`, where it is `0`; `x ^ 0 = 1`.
example (x : ℝ) : x ^ (1 / 2) = 1 := by
  norm_num

-- Exercise 14)
example (x : ℝ) (hx : 0 ≤ x) : (x ^ ((1 : ℝ) / 2)) ^ 2 = x := by
  rw [← Real.sqrt_eq_rpow, Real.sq_sqrt hx]

-- Exercise 15)
example (x : ℝ) (n : ℕ) : x ^ (n : ℝ) = x ^ n := by
  exact Real.rpow_natCast x n

-- Exercises 16 to 19)
example : (∞ : ℝ≥0∞) + 3 = ∞ := by
  simp

example : (0 : ℝ≥0∞) * ∞ = 0 := by
  simp

example (a : ℝ≥0∞) : a + ∞ = ∞ := by
  simp

example : (∞ : ℝ≥0∞).toReal = 0 := by
  simp

-- Exercise 20)
example (n : ℕ) (h : 1 ≤ n) : ((n - 1 : ℕ) : ℤ) = (n : ℤ) - 1 := by
  omega

-- Exercise 21)
example (n : ℕ) (h : 1 ≤ n) : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
  rw [Nat.cast_sub h]
  simp

-- Exercise 22) The left side: `7 / 2 = 3` in `ℕ`, then cast.
example : ((7 / 2 : ℕ) : ℝ) ≠ 7 / 2 := by
  norm_num
