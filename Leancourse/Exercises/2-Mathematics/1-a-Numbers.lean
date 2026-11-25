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
| `norm_cast`                | normalise casts, often closing the goal       |
| `exact_mod_cast h`         | `exact h`, up to casts                        |
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

/-! ## Part 6: Casts

A cast is a coercion between number types (chapter 1.7, *Coercions*).
The chain is `ℕ → ℤ → ℚ → ℝ → ℂ`. A goal can fill up with `↑`s, and
then `ring` or `linarith` do not fire: a cast of a sum is not a sum
of casts. Three tactics tidy this up:

- `push_cast` moves `↑` inwards, towards the leaves (sheet `1.1-c`);
- `norm_cast` normalises and often closes the goal outright;
- `exact_mod_cast h` is `exact h`, up to casts.
-/

-- Exercise 20) The hypothesis is already cast-free inside; push the
-- cast in the goal inwards and finish.
example (n m : ℕ) (h : (n : ℤ) + m = 10) : (↑(n + m) : ℤ) = 10 := by
  sorry

-- Exercise 21) `ring` alone fails here -- the left side is a cast of
-- a sum, the right side a sum of casts. Fix that first.
example (n m : ℕ) : ((n + m : ℕ) : ℤ) ^ 2
    = (n : ℤ) ^ 2 + 2 * n * m + (m : ℤ) ^ 2 := by
  sorry

-- Exercise 22) An inequality that survives the cast.
example (n : ℕ) (h : n < 5) : (n : ℤ) < 5 := by
  sorry

-- Exercise 23) One tactic closes this.
example (n : ℕ) : ((n : ℤ) = 0) ↔ n = 0 := by
  sorry

-- Exercise 24) Two steps up the chain at once.
example (a b : ℕ) (h : (a : ℚ) = b) : a = b := by
  sorry

-- Exercise 25) Subtraction is the dangerous one, because `ℕ` cuts
-- off at zero. With `1 ≤ n` the statement is true; `omega` knows
-- both `ℕ` and `ℤ` and handles the casts itself.
example (n : ℕ) (h : 1 ≤ n) : ((n - 1 : ℕ) : ℤ) = (n : ℤ) - 1 := by
  sorry

-- Without the hypothesis the statement is false: for `n = 0` the
-- left side is `0` and the right side `-1`. Uncomment and watch
-- `omega` refuse:
-- example (n : ℕ) : ((n - 1 : ℕ) : ℤ) = (n : ℤ) - 1 := by omega

-- Exercise 26) `(Nat.even_mul_succ_self n).two_dvd` gives
-- `2 ∣ n * (n + 1)`; then `Nat.cast_div`, `push_cast`, `ring`.
example (n : ℕ) :
    ((n * (n + 1) / 2 : ℕ) : ℝ) = n * (n + 1) / 2 := by
  sorry

-- Exercise 27) For `ℝ`, rewrite with `Nat.cast_sub h` first.
example (n : ℕ) (h : 1 ≤ n) : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
  sorry

-- Exercise 28) Which side is computed in `ℕ`?
example : ((7 / 2 : ℕ) : ℝ) ≠ 7 / 2 := by
  sorry

/-! ## Part 7: More casts

Read the section *Casts* of chapter 2.1 first. Three new tactics,
and `norm_cast` on a hypothesis:

- `zify [h]` moves a goal from `ℕ` to `ℤ`. A subtraction `n - m`
  becomes `↑n - ↑m` only if `h : m ≤ n` is in the list.
- `norm_cast at h ⊢` removes casts from `h` and from the goal.
- `lift x to ℝ≥0 using h` replaces `x : ℝ` by `↑x` with `x : ℝ≥0`.
  Here `h : 0 ≤ x`. For `a : ℝ≥0∞` the condition is `a ≠ ∞`.
- `positivity` proves `0 < e` or `0 ≤ e` from the shape of `e`:
  squares, sums and products of positive terms, casts from `ℕ`.
-/

-- Exercise 29) `ring` fails in `ℕ`; `zify` needs both `≤` facts.
example (n : ℕ) (h : 1 ≤ n) : (n - 1) * (n + 1) = n ^ 2 - 1 := by
  sorry

-- Exercise 30) Remove the casts from `h`.
example (m n : ℕ) (h : (m : ℝ) + 1 ≤ n) : m < n := by
  sorry

-- Exercise 31) `omega` knows `Int.toNat`.
example (k : ℤ) : (k.toNat : ℤ) = max k 0 := by
  sorry

-- Exercise 32) `rw [Int.floor_eq_iff]`.
example (n : ℤ) : ⌊(n : ℝ) + 1 / 2⌋ = n := by
  sorry

-- Exercise 33) Which hypothesis excludes the junk value?
example (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    (ENNReal.ofReal (x * y)).toReal = x * y := by
  sorry

-- Exercise 34) Lift both to `ℝ≥0`, then `norm_cast at h ⊢`.
example (a b : ℝ≥0∞) (ha : a ≠ ∞) (hb : b ≠ ∞)
    (h : a.toReal < b.toReal) : a < b := by
  sorry

-- Exercise 35) Without `ha` it is false. Try `a = ∞`.
example : ¬ ∀ a b : ℝ≥0∞, a.toReal < b.toReal → a < b := by
  sorry

-- Exercise 36) `Real.toNNReal_add`.
example (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    (x + y).toNNReal = x.toNNReal + y.toNNReal := by
  sorry

-- Exercise 37) Without the hypotheses it is false. Try `1` and `-1`.
example : ¬ ∀ x y : ℝ, (x + y).toNNReal = x.toNNReal + y.toNNReal := by
  sorry

-- Exercise 38)
example (x : ℝ) (n : ℕ) : 0 < (n : ℝ) + 1 + x ^ 2 := by
  sorry
