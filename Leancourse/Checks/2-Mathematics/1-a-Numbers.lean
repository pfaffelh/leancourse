import Mathlib

/-!
# (witness) 2.1-a -- Numbers

*Notes chapter 2.1, week 10.* Exercises 1, 2, 5, 8 and 11 change the
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
example (n : ℕ) :
    ((n * (n + 1) / 2 : ℕ) : ℝ) = n * (n + 1) / 2 := by
  rw [Nat.cast_div (Nat.even_mul_succ_self n).two_dvd (by norm_num)]
  push_cast
  ring

-- Exercise 21)
example (n : ℕ) (h : 1 ≤ n) : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
  rw [Nat.cast_sub h]
  simp

-- Exercise 22) The left side: `7 / 2 = 3` in `ℕ`, then cast.
example : ((7 / 2 : ℕ) : ℝ) ≠ 7 / 2 := by
  norm_num

-- Exercise 23)
example (n : ℕ) (h : 1 ≤ n) : (n - 1) * (n + 1) = n ^ 2 - 1 := by
  have h2 : 1 ≤ n ^ 2 := Nat.one_le_pow _ _ h
  zify [h, h2]
  ring

-- Exercise 24)
example (m n : ℕ) (h : (m : ℝ) + 1 ≤ n) : m < n := by
  norm_cast at h

-- Exercise 25)
example (k : ℤ) : (k.toNat : ℤ) = max k 0 := by
  omega

-- Exercise 26)
example (n : ℤ) : ⌊(n : ℝ) + 1 / 2⌋ = n := by
  rw [Int.floor_eq_iff]
  constructor <;> linarith

-- Exercise 27) `hx` and `hy` give `0 ≤ x * y`.
example (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    (ENNReal.ofReal (x * y)).toReal = x * y := by
  exact ENNReal.toReal_ofReal (mul_nonneg hx hy)

-- Exercise 28)
example (a b : ℝ≥0∞) (ha : a ≠ ∞) (hb : b ≠ ∞)
    (h : a.toReal < b.toReal) : a < b := by
  lift a to ℝ≥0 using ha
  lift b to ℝ≥0 using hb
  norm_cast at h ⊢

-- Exercise 29) `(∞).toReal = 0 < 1`, but `∞ < 1` is false.
example : ¬ ∀ a b : ℝ≥0∞, a.toReal < b.toReal → a < b := by
  intro h
  have := h ∞ 1 (by simp)
  simp at this

-- Exercise 30)
example (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    (x + y).toNNReal = x.toNNReal + y.toNNReal := by
  exact Real.toNNReal_add hx hy

-- Exercise 31) Left side `0`, right side `1 + 0`.
example : ¬ ∀ x y : ℝ, (x + y).toNNReal = x.toNNReal + y.toNNReal := by
  intro h
  have := h 1 (-1)
  rw [Real.toNNReal_of_nonpos (by norm_num : (-1 : ℝ) ≤ 0)] at this
  norm_num at this

-- Exercise 32)
example (x : ℝ) (n : ℕ) : 0 < (n : ℝ) + 1 + x ^ 2 := by
  positivity
