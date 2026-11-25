import Mathlib

/-!
# 2.1-a -- Numbers

*Notes chapter 2.1, week 10.*

Each number type is one of the type formers of part 1: `ℤ` is
inductive, `ℚ` and `ℂ` are structures, `ℝ≥0` is a subtype, `ℝ≥0∞`
is `Option ℝ≥0`. Read chapter 2.1 first.

`ℝ≥0` and `ℝ≥0∞` need the line `open scoped NNReal ENNReal` below.
`∞` is typed `\infty`.

## Introduced here

| tactic                     | use it when                                   |
|----------------------------|-----------------------------------------------|
| `zify [h]`                 | a goal in `ℕ` with `-` is easier in `ℤ`       |
| `norm_cast at h ⊢`         | remove casts from `h` and from the goal       |
| `lift x to ℝ≥0 using h`    | `x` lies in the image of the cast, by `h`     |
| `positivity`               | goal `0 < e` or `0 ≤ e`, by the shape of `e`  |

## Tactics from earlier sheets

| sheet   | tactics                                                      |
|---------|--------------------------------------------------------------|
| `L-a`   | `intro`, `exact`                                             |
| `L-b`   | `constructor`                                                |
| `1.1-a` | `rfl`, `rw`                                                  |
| `1.1-b` | `decide`, `<;>`                                              |
| `L-f`   | `have`                                                       |
| `1.1-c` | `norm_num`, `simp`, `omega`, `ring`, `linarith`, `push_cast` |
| `1.7-b` | `norm_cast`                                                  |
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

-- Exercise 20) `(Nat.even_mul_succ_self n).two_dvd` gives
-- `2 ∣ n * (n + 1)`; then `Nat.cast_div`, `push_cast`, `ring`.
example (n : ℕ) :
    ((n * (n + 1) / 2 : ℕ) : ℝ) = n * (n + 1) / 2 := by
  sorry

-- Exercise 21) For `ℝ`, rewrite with `Nat.cast_sub h` first.
example (n : ℕ) (h : 1 ≤ n) : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
  sorry

-- Exercise 22) Which side is computed in `ℕ`?
example : ((7 / 2 : ℕ) : ℝ) ≠ 7 / 2 := by
  sorry

/-! ## Part 7: More casts

Read the section *Casts* of chapter 2.1 first. Four new tactics:

- `zify [h]` moves a goal from `ℕ` to `ℤ`. A subtraction `n - m`
  becomes `↑n - ↑m` only if `h : m ≤ n` is in the list.
- `norm_cast at h ⊢` removes casts from `h` and from the goal.
- `lift x to ℝ≥0 using h` replaces `x : ℝ` by `↑x` with `x : ℝ≥0`.
  Here `h : 0 ≤ x`. For `a : ℝ≥0∞` the condition is `a ≠ ∞`.
- `positivity` proves `0 < e` or `0 ≤ e` from the shape of `e`:
  squares, sums and products of positive terms, casts from `ℕ`.
-/

-- Exercise 23) `ring` fails in `ℕ`; `zify` needs both `≤` facts.
example (n : ℕ) (h : 1 ≤ n) : (n - 1) * (n + 1) = n ^ 2 - 1 := by
  sorry

-- Exercise 24) Remove the casts from `h`.
example (m n : ℕ) (h : (m : ℝ) + 1 ≤ n) : m < n := by
  sorry

-- Exercise 25) `omega` knows `Int.toNat`.
example (k : ℤ) : (k.toNat : ℤ) = max k 0 := by
  sorry

-- Exercise 26) `rw [Int.floor_eq_iff]`.
example (n : ℤ) : ⌊(n : ℝ) + 1 / 2⌋ = n := by
  sorry

-- Exercise 27) Which hypothesis excludes the junk value?
example (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    (ENNReal.ofReal (x * y)).toReal = x * y := by
  sorry

-- Exercise 28) Lift both to `ℝ≥0`, then `norm_cast at h ⊢`.
example (a b : ℝ≥0∞) (ha : a ≠ ∞) (hb : b ≠ ∞)
    (h : a.toReal < b.toReal) : a < b := by
  sorry

-- Exercise 29) Without `ha` it is false. Try `a = ∞`.
example : ¬ ∀ a b : ℝ≥0∞, a.toReal < b.toReal → a < b := by
  sorry

-- Exercise 30) `Real.toNNReal_add`.
example (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    (x + y).toNNReal = x.toNNReal + y.toNNReal := by
  sorry

-- Exercise 31) Without the hypotheses it is false. Try `1` and `-1`.
example : ¬ ∀ x y : ℝ, (x + y).toNNReal = x.toNNReal + y.toNNReal := by
  sorry

-- Exercise 32)
example (x : ℝ) (n : ℕ) : 0 < (n : ℝ) + 1 + x ^ 2 := by
  sorry
