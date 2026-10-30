import Mathlib

/-!
# 2.1-a -- Numbers

*Notes chapter 2.1, week 9.*

Each number type is one of the type formers of part 1: `ℤ` is
inductive, `ℚ` and `ℂ` are structures, `ℝ≥0` is a subtype, `ℝ≥0∞`
is `Option ℝ≥0`. Read chapter 2.1 first.

`ℝ≥0` and `ℝ≥0∞` need the line `open scoped NNReal ENNReal` below.
`∞` is typed `\infty`.

`omega`, `simp`, `norm_num`, `decide` and the casts tactics are
known from part 1; `exact?` and `rw?` from `2.0-a`.
-/

open scoped NNReal ENNReal

/-! ## Part 1: How the numbers are built -/

-- Exercise 1) `Int.negSucc n` is `-(n + 1)`. Replace `sorry` by a
-- numeral so that `rfl` works.
example : Int.negSucc 0 = sorry := by
  sorry

-- Exercise 2) A rational number is stored reduced. Find numerator
-- and denominator of `10 / 4` with `#eval`, put them in, and prove
-- both with `norm_num`.
-- #eval (10 / 4 : ℚ).num
example : (10 / 4 : ℚ).num = sorry ∧ (10 / 4 : ℚ).den = sorry := by
  sorry

-- Exercise 3) `x : ℝ≥0` is a pair of a real number and a proof. One
-- term does it.
example (x : ℝ≥0) : 0 ≤ (x : ℝ) := by
  sorry

-- Exercise 4) A complex number is the structure `⟨re, im⟩`.
example (z : ℂ) : z = ⟨z.re, z.im⟩ := by
  sorry

/-! ## Part 2: Arithmetic in `ℕ` and `ℤ` -/

-- Exercise 5) Replace `sorry` by the value, then `decide`.
example : (3 : ℕ) - 5 + 5 = sorry := by
  sorry

-- Exercise 6)
example (n m : ℕ) (h : m ≤ n) : n - m + m = n := by
  sorry

-- Exercise 7) Without the hypothesis it is false. Give a
-- counterexample: `intro h`, then `have := h a b` for suitable
-- `a b`, then `omega`.
example : ¬ ∀ n m : ℕ, n - m + m = n := by
  sorry

-- Exercise 8) Division in `ℤ` rounds down, and the remainder is
-- never negative. Replace both `sorry`s, then `decide`.
example : (-9 : ℤ) / 4 = sorry ∧ (-9 : ℤ) % 4 = sorry := by
  sorry

/-! ## Part 3: Junk values -/

-- Exercise 9)
example (x : ℝ) : x / 0 = 0 := by
  sorry

-- Exercise 10)
example : Real.sqrt (-4) = 0 := by
  sorry

-- Exercise 11) Replace `True` by the hypothesis that makes this
-- true, then find the theorem with `exact?`.
example (a b : ℝ) (h : True) : a / b * b = a := by
  sorry

-- Exercise 12) This one needs no hypothesis. Find the theorem, and
-- check by hand that it holds for `c = 0` too.
example (a b c : ℝ) : (a + b) / c = a / c + b / c := by
  sorry

/-! ## Part 4: Powers -/

-- Exercise 13) Why is this true? Answer in a comment, then prove it.
example (x : ℝ) : x ^ (1 / 2) = 1 := by
  sorry

-- Exercise 14) Here the exponent is a real number. Rewrite with
-- `← Real.sqrt_eq_rpow`, then use `Real.sq_sqrt`.
example (x : ℝ) (hx : 0 ≤ x) : (x ^ ((1 : ℝ) / 2)) ^ 2 = x := by
  sorry

-- Exercise 15) The real power with a natural exponent is the
-- natural power.
example (x : ℝ) (n : ℕ) : x ^ (n : ℝ) = x ^ n := by
  sorry

/-! ## Part 5: `ℝ≥0∞` -/

-- Exercises 16 to 19) `simp` knows the rules for `∞`.
example : (∞ : ℝ≥0∞) + 3 = ∞ := by
  sorry

example : (0 : ℝ≥0∞) * ∞ = 0 := by
  sorry

example (a : ℝ≥0∞) : a + ∞ = ∞ := by
  sorry

example : (∞ : ℝ≥0∞).toReal = 0 := by
  sorry

/-! ## Part 6: Casts -/

-- Exercise 20) `omega` handles casts from `ℕ` to `ℤ`.
example (n : ℕ) (h : 1 ≤ n) : ((n - 1 : ℕ) : ℤ) = (n : ℤ) - 1 := by
  sorry

-- Exercise 21) For `ℝ`, rewrite with `Nat.cast_sub h` first.
example (n : ℕ) (h : 1 ≤ n) : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
  sorry

-- Exercise 22) Which side is computed in `ℕ`?
example : ((7 / 2 : ℕ) : ℝ) ≠ 7 / 2 := by
  sorry
