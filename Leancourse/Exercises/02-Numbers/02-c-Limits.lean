import Mathlib -- import all the tactics

/-
While the last exercises were on natural numbers, we now come to real numbers and their limits. Recall that a sequence of real numbers is some `x : ℕ → ℝ`. We start by a definition:

If `x : ℕ → ℝ` is a sequence of reals and `t : ℝ`, the limit `TendsTo x t` is the assertion that `x n → t` as `n → ∞`. -/
def TendsTo (x : ℕ → ℝ) (t : ℝ) : Prop :=
  ∀ ε > 0, ∃ N : ℕ, ∀ n, N ≤ n → |x n - t| < ε

/-

-- The first statement is very simple, since it only uses the definition of a limit. Note the brackets `{...}`. They mean that these variables are implicit and when using this statement, Lean tries to infer them. In this example, `x` appears on both sides of the statement (in `TendsTo x t`, and in `∀ ε, 0 < ε → ∃ N : ℕ, ∀ n, N ≤ n → |x n - t| < ε`), so Lean should be able to fill this gap. (See manuscript for more details.)
-/
theorem tendsTo_def {x : ℕ → ℝ} {t : ℝ} :
    TendsTo x t ↔ ∀ ε, 0 < ε → ∃ N : ℕ, ∀ n, N ≤ n → |x n - t| < ε := by
  rfl

-- Let us start by showing that a constant sequence has a limit. Note that the first line in the proof unfolds the definition of `TendsTo`.

example (c : ℝ) : TendsTo (fun n ↦ c) c := by
  rw [tendsTo_def]
  intro ε hε
  use 0
  intro n hn
  simp [hε]


-- In the following exercise, there is a chance you need the following:
#check add_sub_add_right_eq_sub

-- Exercise 1: If `x` tends to `t` then `x + c` tends to `t + c`
-- Big hint: Write down the math proof first!
theorem tendsTo_add_const {a : ℕ → ℝ} {t : ℝ} (c : ℝ) (h : TendsTo a t) :
    TendsTo (fun n => a n + c) (t + c) := by
  rw [tendsTo_def] at h ⊢
  sorry

-- In the following exercise, there is a chance you need the following:
#check sub_neg_eq_add
#check neg_add_eq_sub
#check abs_neg
#check neg_sub

-- Exercise 2: If `x` tends to `t` then `-x` tends to `-t`.
-- Big hint: Write down the math proof first!
example {x : ℕ → ℝ} {t : ℝ} (hx : TendsTo x t) : TendsTo (fun n => -x n) (-t) := by
  sorry

/- In concrete examples of series, e.g. `x : ℕ → ℝ := fun n ↦ 1 / n`, one often needs to transform between `n : ℕ` and `n : ℝ`. The reasos is that division is not defined on `ℕ`, so lean has to make sense of an expression like `1/n`. Here, the `norm_cast` tactic can help in order to transform e.g. some `n : ℝ` (which is in fact `∈ ℕ`) to `n : ℕ`. -/

-- Here we use
#check one_div_lt_one_div

example (m n : ℕ) (hm : 0 < m) (hn : 0 < n) (hmn : m < n) : 1/(n : ℝ) < 1/(m : ℝ) := by
  rw [one_div_lt_one_div]
  · norm_cast
  · norm_cast
  · norm_cast

-- Note that the proof can be made shorter using `<;>`. This means that the tactic which follows is applied to all goals.

example (m n : ℕ) (hm : 0 < m) (hn : 0 < n) (hmn : m < n) : 1/(n : ℝ) < 1/(m : ℝ) := by
  rw [one_div_lt_one_div] <;> norm_cast

-- Here is the next list of results which you might need for the upcoming exercise:
#check exists_nat_gt
#check abs_of_nonneg
#check gt_iff_lt
#check one_div_le_one_div_of_le

-- Exercise 3: `1/n` tends to `0`.
example (a : ℕ → ℝ) (ha : ∀ (n : ℕ), a n = 1 / n) : TendsTo a 0 := by
  sorry

-- In the following exercise, there is a chance you need the following:
#check sub_neg_eq_add
#check neg_add_eq_sub
#check abs_neg
#check neg_sub
#check abs_lt

-- We write `max x y` for the maximum of two numbers.

-- Exercise 4: If `x` tends to `t` and `y` tends to `u`, then `x + y` tends to `t + u`.
-- Big hint: Write down the math proof first!
theorem tendsTo_add {x y : ℕ → ℝ} {t u : ℝ} (hx : TendsTo x t) (hy : TendsTo y u) :
    TendsTo (fun n ↦ x n + y n) (t + u) := by
  sorry

-- Exercise 5: If `x` tends to `t` then `x - c` tends to `t - c`.
-- Hint: rewrite `x - c` as `x + (-c)` and reuse `tendsTo_add_const`.
example {x : ℕ → ℝ} {t : ℝ} (c : ℝ) (h : TendsTo x t) :
    TendsTo (fun n => x n - c) (t - c) := by
  sorry

-- Exercise 6: If `x` tends to `t` and `y` tends to `u`, then `x - y`
-- tends to `t - u`.
example {x y : ℕ → ℝ} {t u : ℝ} (hx : TendsTo x t) (hy : TendsTo y u) :
    TendsTo (fun n ↦ x n - y n) (t - u) := by
  sorry

-- Exercise 7: A bounded sequence times one tending to 0 tends to 0.
-- (This is a specialization of the squeeze theorem.)
example (a : ℕ → ℝ) (M : ℝ) (hM : ∀ n, |a n| ≤ M)
    (b : ℕ → ℝ) (hb : TendsTo b 0) :
    TendsTo (fun n => a n * b n) 0 := by
  sorry

-- Exercise 8: A scalar multiple of a convergent sequence is convergent.
example {x : ℕ → ℝ} {t : ℝ} (c : ℝ) (h : TendsTo x t) :
    TendsTo (fun n => c * x n) (c * t) := by
  sorry

-- Exercise 9: The sequence `1 / (n + 1)` tends to 0 (no `0/0` issue).
example : TendsTo (fun n : ℕ => 1 / ((n : ℝ) + 1)) 0 := by
  sorry

-- Exercise 10: Limits are unique. If `x` tends to both `t` and `u`,
-- then `t = u`.
example {x : ℕ → ℝ} {t u : ℝ}
    (ht : TendsTo x t) (hu : TendsTo x u) : t = u := by
  sorry
