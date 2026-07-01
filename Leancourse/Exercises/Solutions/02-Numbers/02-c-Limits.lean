import Mathlib -- import all the tactics

/- Solutions to 02-c-Limits. -/

def TendsTo (x : ℕ → ℝ) (t : ℝ) : Prop :=
  ∀ ε > 0, ∃ N : ℕ, ∀ n, N ≤ n → |x n - t| < ε

theorem tendsTo_def {x : ℕ → ℝ} {t : ℝ} :
    TendsTo x t ↔ ∀ ε, 0 < ε → ∃ N : ℕ, ∀ n, N ≤ n → |x n - t| < ε := by
  rfl

example (c : ℝ) : TendsTo (fun n ↦ c) c := by
  rw [tendsTo_def]
  intro ε hε
  use 0
  intro n hn
  simp [hε]

-- Exercise 1
theorem tendsTo_add_const {a : ℕ → ℝ} {t : ℝ} (c : ℝ) (h : TendsTo a t) :
    TendsTo (fun n => a n + c) (t + c) := by
  rw [tendsTo_def] at h ⊢
  intro ε hε
  obtain ⟨N, hN⟩ := h ε hε
  refine ⟨N, fun n hn => ?_⟩
  show |a n + c - (t + c)| < ε
  rw [show a n + c - (t + c) = a n - t from by ring]
  exact hN n hn

-- Exercise 2
theorem tendsTo_neg {x : ℕ → ℝ} {t : ℝ} (hx : TendsTo x t) :
    TendsTo (fun n => -x n) (-t) := by
  rw [tendsTo_def] at hx ⊢
  intro ε hε
  obtain ⟨N, hN⟩ := hx ε hε
  refine ⟨N, fun n hn => ?_⟩
  show |-x n - -t| < ε
  rw [show -x n - -t = -(x n - t) from by ring, abs_neg]
  exact hN n hn

-- Exercise 3
example (a : ℕ → ℝ) (ha : ∀ (n : ℕ), a n = 1 / n) : TendsTo a 0 := by
  rw [tendsTo_def]
  intro ε hε
  obtain ⟨N, hN⟩ := exists_nat_gt (1 / ε)
  refine ⟨N + 1, fun n hn => ?_⟩
  rw [ha n, sub_zero]
  have hnpos : (0 : ℝ) < n := by
    have : (1 : ℕ) ≤ n := le_trans (Nat.le_add_left 1 N) hn
    exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one this
  rw [abs_of_pos (by positivity), div_lt_iff₀ hnpos]
  have hNn : (N : ℝ) ≤ n := by exact_mod_cast le_trans (Nat.le_succ N) hn
  have : (1 : ℝ) / ε < n := lt_of_lt_of_le hN hNn
  rw [div_lt_iff₀ hε] at this
  linarith

-- Exercise 4
theorem tendsTo_add {x y : ℕ → ℝ} {t u : ℝ} (hx : TendsTo x t) (hy : TendsTo y u) :
    TendsTo (fun n ↦ x n + y n) (t + u) := by
  rw [tendsTo_def] at *
  intro ε hε
  obtain ⟨Nx, hNx⟩ := hx (ε / 2) (by linarith)
  obtain ⟨Ny, hNy⟩ := hy (ε / 2) (by linarith)
  refine ⟨max Nx Ny, fun n hn => ?_⟩
  have h1 := hNx n (le_trans (le_max_left _ _) hn)
  have h2 := hNy n (le_trans (le_max_right _ _) hn)
  show |x n + y n - (t + u)| < ε
  calc |x n + y n - (t + u)| = |(x n - t) + (y n - u)| := by
        rw [show x n + y n - (t + u) = (x n - t) + (y n - u) from by ring]
    _ ≤ |x n - t| + |y n - u| := abs_add_le _ _
    _ < ε := by linarith

-- Exercise 5
example {x : ℕ → ℝ} {t : ℝ} (c : ℝ) (h : TendsTo x t) :
    TendsTo (fun n => x n - c) (t - c) := by
  have h2 := tendsTo_add_const (-c) h
  simp only [← sub_eq_add_neg] at h2
  exact h2

-- Exercise 6
example {x y : ℕ → ℝ} {t u : ℝ} (hx : TendsTo x t) (hy : TendsTo y u) :
    TendsTo (fun n ↦ x n - y n) (t - u) := by
  have hneg := tendsTo_neg hy
  have hadd := tendsTo_add hx hneg
  simp only [← sub_eq_add_neg] at hadd
  exact hadd

-- Exercise 7
example (a : ℕ → ℝ) (M : ℝ) (hM : ∀ n, |a n| ≤ M)
    (b : ℕ → ℝ) (hb : TendsTo b 0) :
    TendsTo (fun n => a n * b n) 0 := by
  rw [tendsTo_def] at *
  intro ε hε
  have hM0 : 0 ≤ M := le_trans (abs_nonneg (a 0)) (hM 0)
  obtain ⟨N, hN⟩ := hb (ε / (M + 1)) (by positivity)
  refine ⟨N, fun n hn => ?_⟩
  have hbn := hN n hn
  rw [sub_zero] at hbn
  show |a n * b n - 0| < ε
  rw [sub_zero, abs_mul]
  calc |a n| * |b n| ≤ M * |b n| :=
        mul_le_mul_of_nonneg_right (hM n) (abs_nonneg _)
    _ ≤ (M + 1) * |b n| :=
        mul_le_mul_of_nonneg_right (by linarith) (abs_nonneg _)
    _ < (M + 1) * (ε / (M + 1)) :=
        mul_lt_mul_of_pos_left hbn (by positivity)
    _ = ε := by field_simp

-- Exercise 8
example {x : ℕ → ℝ} {t : ℝ} (c : ℝ) (h : TendsTo x t) :
    TendsTo (fun n => c * x n) (c * t) := by
  rw [tendsTo_def] at *
  intro ε hε
  obtain ⟨N, hN⟩ := h (ε / (|c| + 1)) (by positivity)
  refine ⟨N, fun n hn => ?_⟩
  have hxn := hN n hn
  show |c * x n - c * t| < ε
  rw [show c * x n - c * t = c * (x n - t) from by ring, abs_mul]
  calc |c| * |x n - t| ≤ (|c| + 1) * |x n - t| :=
        mul_le_mul_of_nonneg_right (by linarith) (abs_nonneg _)
    _ < (|c| + 1) * (ε / (|c| + 1)) :=
        mul_lt_mul_of_pos_left hxn (by positivity)
    _ = ε := by field_simp

-- Exercise 9
example : TendsTo (fun n : ℕ => 1 / ((n : ℝ) + 1)) 0 := by
  rw [tendsTo_def]
  intro ε hε
  obtain ⟨N, hN⟩ := exists_nat_gt (1 / ε)
  refine ⟨N, fun n hn => ?_⟩
  show |1 / ((n : ℝ) + 1) - 0| < ε
  rw [sub_zero, abs_of_pos (by positivity), div_lt_iff₀ (by positivity)]
  have hNn : (N : ℝ) ≤ n := by exact_mod_cast hn
  have h1 : (1 : ℝ) / ε < (n : ℝ) + 1 := by linarith [lt_of_lt_of_le hN hNn]
  rw [div_lt_iff₀ hε] at h1
  linarith

-- Exercise 10
example {x : ℕ → ℝ} {t u : ℝ}
    (ht : TendsTo x t) (hu : TendsTo x u) : t = u := by
  by_contra hne
  rw [tendsTo_def] at ht hu
  have hd : 0 < |t - u| := abs_pos.mpr (sub_ne_zero.mpr hne)
  obtain ⟨N1, hN1⟩ := ht (|t - u| / 2) (by linarith)
  obtain ⟨N2, hN2⟩ := hu (|t - u| / 2) (by linarith)
  set m := max N1 N2 with hm
  have h1 := hN1 m (le_max_left _ _)
  have h2 := hN2 m (le_max_right _ _)
  have htri : |t - u| ≤ |x m - t| + |x m - u| := by
    calc |t - u| = |(t - x m) + (x m - u)| := by
          rw [show t - u = (t - x m) + (x m - u) from by ring]
      _ ≤ |t - x m| + |x m - u| := abs_add_le _ _
      _ = |x m - t| + |x m - u| := by rw [abs_sub_comm t (x m)]
  linarith
