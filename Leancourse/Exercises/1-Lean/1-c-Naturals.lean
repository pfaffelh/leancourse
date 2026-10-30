import Mathlib

/-!
# 1.1-c -- Arithmetic and induction on `ℕ`

*Notes chapter 1.1, week 4.*

On sheet `1.1-a` everything about `ℕ` was built by hand. Here we use
what Mathlib already proves about `ℕ`, and the tactics that do the
arithmetic for us.

## Tactics introduced here

| tactic                 | use it when                                         |
|------------------------|-----------------------------------------------------|
| `cases n with`         | split `n : ℕ` into `zero` and `succ k`              |
| `rw [lemma]`           | rewrite with an equation from Mathlib               |
| `nth_rw k [lemma]`     | rewrite only the `k`-th occurrence                  |
| `calc`                 | a chain of steps `a = b`, `b = c`, ... or with `≤`  |
| `ring`                 | an equation that holds in every commutative ring    |
| `norm_num`             | numerals: `123 * 321 = 39483`, `1 / 2 < 1`          |
| `linarith`             | a linear (in)equality that follows from hypotheses  |
| `simp`, `simp?`        | simplify with Mathlib's `@[simp]` lemmas            |
| `induction n with`     | induction on `n : ℕ`                                |
| `omega`                | linear arithmetic on `ℕ` and `ℤ`                    |
-/

open Nat

/-! `open Nat` lets us write `succ` instead of `Nat.succ`. Put the cursor
on a name and press `F12` to see its definition. -/

/-! ## Part 1: Cases on `ℕ`

`cases n` splits `n : ℕ` into its two constructors, as `cases b` did
for `b : Bool` on sheet `1.1-b`. Each case gets its branch and names
its variables. -/

example (n : ℕ) : n = 0 ∨ ∃ k : ℕ, n = succ k := by
  cases n with
  | zero =>
    left
    rfl
  | succ k =>
    right
    use k

/-! Mathlib has this as a lemma: -/

example (n : ℕ) (hn : n ≠ 0) : ∃ k : ℕ, n = succ k :=
  exists_eq_succ_of_ne_zero hn

-- Exercise 1) There are two routes. Either work with
-- `exists_eq_succ_of_ne_zero` twice, or name the witness with `use`
-- and let `omega` check the arithmetic.
example (n : ℕ) (h : n > 1) : ∃ k : ℕ, n = k + 2 := by
  sorry

/-! ## Part 2: Rewriting and `calc`

`rw [h]` with `h : a = b` replaces `a` by `b`; `rw [← h]` replaces `b`
by `a`. Mathlib's lemmas about `+`, `*` and `^` are equations of this
kind. These are the ones used below: -/

#check add_zero   -- a + 0 = a
#check zero_add   -- 0 + a = a
#check add_comm   -- a + b = b + a
#check add_assoc  -- a + b + c = a + (b + c)
#check mul_one    -- a * 1 = a
#check one_mul    -- 1 * a = a
#check mul_comm   -- a * b = b * a
#check mul_add    -- a * (b + c) = a * b + a * c
#check add_mul    -- (a + b) * c = a * c + b * c
#check pow_two    -- a ^ 2 = a * a

example (m n : ℕ) : m + n = n + m + 0 := by
  rw [add_zero, add_comm]

/-! `calc` writes the same proof as a chain. Each step is a goal of
its own, with its own `by`. -/

example (m n : ℕ) : m + n = n + m + 0 := by
  calc m + n = n + m := by rw [add_comm]
    _ = n + m + 0 := by rw [add_zero]

/-! `nth_rw k [h]` rewrites only the `k`-th place where `h` matches.
Here `rw [← one_mul n]` would turn both `n` into `1 * n` at once. -/

lemma double (n : ℕ) : n + n = 2 * n := by
  calc n + n = 1 * n + n := by nth_rw 1 [← one_mul n]
    _ = 1 * n + 1 * n := by nth_rw 2 [← one_mul n]
    _ = (1 + 1) * n := by rw [add_mul]
    _ = 2 * n := by rfl

lemma binom1 (n : ℕ) : (n + 1) ^ 2 = n ^ 2 + 2 * n + 1 := by
  calc (n + 1) ^ 2 = (n + 1) * (n + 1) := by rw [pow_two]
    _ = (n + 1) * n + (n + 1) * 1 := by rw [mul_add]
    _ = n * n + 1 * n + (n + 1) := by rw [add_mul, mul_one (n + 1)]
    _ = n ^ 2 + n + (n + 1) := by rw [one_mul, ← pow_two]
    _ = n ^ 2 + (n + n + 1) := by rw [add_assoc, ← add_assoc n n 1]
    _ = n ^ 2 + 2 * n + 1 := by rw [← add_assoc, ← double]

-- Exercise 2) With `rw` only.
example (a b c : ℕ) : (a + b) * c = c * a + b * c := by
  sorry

-- Exercise 3) With `calc`, one lemma per step.
example (m n : ℕ) : m * (n + 1) + 0 = m + m * n := by
  sorry

/-! ## Part 3: Four automatic tactics

Rewriting each rule by hand is slow. Four tactics do it for us:

* `ring` proves equations that hold in every commutative ring, such as
  the binomial formula. It does not use hypotheses.
* `norm_num` computes with numerals.
* `linarith` proves linear equations and inequalities from the
  hypotheses.
* `simp` rewrites with the lemmas Mathlib marks `@[simp]`, such as
  `n + 0 = n`. `simp?` shows which lemmas it used, `simp at h` works on
  a hypothesis. -/

example (n : ℕ) : (n + 1) ^ 2 = n ^ 2 + 2 * n + 1 := by
  ring

example : 123 * 321 = 39483 := by
  norm_num

example (k m n : ℕ) (h₁ : k ≤ m + n) (h₂ : m < n) : k < 2 * n := by
  linarith

example (n : ℕ) : n + 0 + 0 = 0 + 0 + n := by
  simp

-- Exercises 4 to 8) One tactic each. Which one?
example : 0 < 1 := by
  sorry

example (n : ℕ) : n * (n + 1) * (n + 2) = n ^ 3 + 3 * n ^ 2 + 2 * n := by
  sorry

example : 1 ^ 100 = 100 / 100 := by
  sorry

example (k m n : ℕ) (h₁ : k + 2 ≤ m) (h₂ : m < n) : k + 3 ≤ n := by
  sorry

example (n : ℕ) : 0 * n + n * 1 + 0 = n := by
  sorry

/-! ## Part 4: Finding the lemma

Part of each task is to find the lemma that does the work, with
`exact?` or by guessing its name. -/

example (x y : ℕ) : x ^ (y + 1) = x * x ^ y :=
  Nat.pow_succ'

-- Exercise 9)
example (m n : ℕ) : m ^ (n + 2) = m * m ^ n * m := by
  sorry

-- Exercise 10) A lemma saying `a ≤ a ^ n` for `n ≠ 0` exists.
example (n : ℕ) : n ≤ n ^ 2 := by
  sorry

-- Exercise 11) Three inequalities in a row: `have` each of them, then
-- `le_trans`. For `n ^ 2 ≤ n ^ 3`, the case `n = 0` is separate.
#check Nat.pow_le_pow_left   -- m ≤ n → m ^ i ≤ n ^ i
#check Nat.pow_le_pow_right  -- n > 0 → i ≤ j → n ^ i ≤ n ^ j
#check le_trans              -- a ≤ b → b ≤ c → a ≤ c

example (k m n : ℕ) (hkm : k ≤ m) (hmn : m ≤ n) : k ^ 2 ≤ n ^ 3 := by
  sorry

-- Exercise 12) For `0 ≤ x`, a power is at most `1` exactly when `x`
-- is. One direction is a lemma; for the other, assume `1 < x` with
-- `by_contra` and `push Not`.
#check pow_le_one₀   -- 0 ≤ a → a ≤ 1 → a ^ n ≤ 1
#check one_lt_pow₀   -- 1 < a → n ≠ 0 → 1 < a ^ n

example (x : ℝ) (n : ℕ) (h : 0 ≤ x) : x ^ (n + 1) ≤ 1 ↔ x ≤ 1 := by
  sorry

/-! ## Part 5: Induction

`induction n with` is `cases n with` plus an induction hypothesis in
the `succ` case. -/

example (n : ℕ) : n = 0 ∨ ∃ k : ℕ, n = succ k := by
  induction n with
  | zero =>
    left
    rfl
  | succ n hn =>
    right
    use n

-- Exercise 13) In the `succ` case, split the induction hypothesis with
-- `obtain (hk | hk) := hn`.
example (n : ℕ) : (∃ k : ℕ, n = 2 * k) ∨ (∃ k : ℕ, n = 2 * k + 1) := by
  induction n with
  | zero =>
    sorry
  | succ n hn =>
    sorry

/-! In the next exercise `n : ℕ` appears inside a statement about `ℝ`.
Lean inserts the map `ℕ → ℝ` and shows it as `↑n`. `push_cast` turns
`↑(n + 1)` into `↑n + 1`. -/

example (x : ℝ) (d : ℕ) : 0 ≤ (d : ℝ) * x ^ 2 := by
  have h₀ : 0 ≤ (d : ℝ) := Nat.cast_nonneg d
  exact mul_nonneg h₀ (sq_nonneg x)

-- Exercise 14) Bernoulli's inequality for `0 ≤ x`. In the `succ` case,
-- first show `1 ≤ (1 + x) ^ n` (lemma `one_le_pow₀`), then a `calc`.
#check one_le_pow₀                  -- 1 ≤ a → 1 ≤ a ^ n
#check mul_le_mul_of_nonneg_right   -- b ≤ c → 0 ≤ a → b * a ≤ c * a

example (n : ℕ) (x : ℝ) (h : 0 ≤ x) : (1 : ℝ) + n * x ≤ (1 + x) ^ n := by
  sorry

-- Exercise 15)
example (n : ℕ) : n + 1 ≤ 2 ^ n := by
  sorry

/-! ## Part 6: Sums

`∑ k ∈ Finset.range n, f k` is the sum of `f k` for `k < n`, typed
`\sum`; `Finset.range n` is `{0, …, n - 1}`. Finite sets are in chapter
2.2; here the notation is enough, together with
`Finset.sum_range_succ`, which splits off the last summand. -/

#check Finset.sum_range_succ

-- Exercise 16)
example (n : ℕ) : 2 * (∑ k ∈ Finset.range (n + 1), k) = n * (n + 1) := by
  induction n with
  | zero =>
    sorry
  | succ n hn =>
    sorry

-- Exercise 17) The sum of the first `n` odd numbers.
example (n : ℕ) :
    (∑ k ∈ Finset.range n, (2 * k + 1)) = n ^ 2 := by
  sorry

/-! ## Part 7: `omega`

`omega` decides linear arithmetic over `ℕ` and `ℤ`, including
subtraction on `ℕ` and division and remainder by numerals. -/

-- Exercise 18) Division with remainder: name `q` and `r` with `use`.
example (n : ℕ) : ∃ q r : ℕ, n = 2 * q + r ∧ r < 2 := by
  sorry

-- Exercise 19)
example (n : ℕ) (h : 0 < n) : n - 1 < n := by
  sorry
