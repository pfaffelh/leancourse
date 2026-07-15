import Mathlib

/-
# Exercise Sheet 7b: The `conv` tactic -- Solutions
-/

-- 1. Rewrite only the first `a`.
example (a b : ℕ) (h : a = b) : a + a = b + a := by
  conv_lhs => lhs; rw [h]

-- 2. Rewrite only the second `a`.
example (a b : ℕ) (h : a = b) : a + a = a + b := by
  conv_lhs => rhs; rw [h]

-- 3. Rewrite under the `λ`-binder.
example (f : ℕ → ℕ) (h : ∀ n, f n = 0) :
    (fun n => f n + 1) = (fun n => 0 + 1) := by
  conv_lhs => ext n; rw [h]

-- 4. Simplify the hypothesis with `conv at h`, then finish.
example (a b : ℕ) (h : a + 0 = b) : a = b := by
  conv at h => lhs; rw [add_zero]
  exact h

-- 5. Reach the first `a` deep inside with `enter`.
example (a b : ℕ) (h : a = b) :
    (a + 1) + (a + 2) = (b + 1) + (a + 2) := by
  conv_lhs => enter [1,1]; rw [h]
