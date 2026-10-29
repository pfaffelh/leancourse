import Mathlib

/-! Witness for `2.0-a`. Exercise 7 replaces `True` by the hypothesis. -/

example (a b : ℝ) : |a * b| = |a| * |b| := by
  exact abs_mul a b

-- Exercise 1)
example (x : ℝ) : 0 ≤ x ^ 2 := by
  exact sq_nonneg x

-- Exercise 2)
example (a b : ℕ) (h : a ∣ b) (hb : 0 < b) : a ≤ b := by
  exact Nat.le_of_dvd hb h

-- Exercise 3)
example (p : ℕ) (hp : p.Prime) : 2 ≤ p := by
  exact hp.two_le

-- Exercise 4)
example (f g : ℝ → ℝ) (hf : Monotone f) (hg : Monotone g) :
    Monotone (f ∘ g) := by
  exact Monotone.comp hf hg

-- Exercise 5)
example (n : ℕ) : n < 2 ^ n := by
  exact Nat.lt_two_pow_self

-- Exercise 6)
example (x : ℝ) (hx : 0 < x) : 0 < x + x ^ 2 := by
  have h : 0 < x ^ 2 := by exact sq_pos_of_pos hx
  exact lt_add_of_pos_of_lt hx h

-- Exercise 7)
example (x : ℝ) (hx : 0 ≤ x) : Real.sqrt x ^ 2 = x := by
  exact Real.sq_sqrt hx

example (x y : ℝ) : Real.exp (x + y) = Real.exp x * Real.exp y := by
  rw [Real.exp_add]

-- Exercise 8)
example (x : ℝ) : Real.exp (2 * x) = Real.exp x ^ 2 := by
  rw [two_mul, Real.exp_add, sq]

-- Exercise 9)
example (x : ℝ) : Real.log (x ^ 2) = 2 * Real.log x := by
  rw [Real.log_pow]
  norm_num

#check Real.log_neg_eq_log
#check Real.log_zero

-- Exercise 10)
example (n : ℕ) : ∑ i ∈ Finset.range (n + 1), i = n * (n + 1) / 2 := by
  rw [Finset.sum_range_id]
  simp [mul_comm]

-- Exercise 11)
example (a b : ℝ) (h : a * b = 0) (ha : a ≠ 0) : b = 0 := by
  rw [mul_eq_zero] at h
  obtain h | h := h
  · exact absurd h ha
  · exact h

example (a b : ℝ) (h : a * b = 0) (ha : a ≠ 0) : b = 0 := by
  exact (mul_eq_zero_iff_left ha).mp h

-- Exercise 12)
example (a b : ℝ) (ha : 0 < a) (hb : 0 < b) : 0 < a * b := by
  exact mul_pos ha hb

-- Exercise 13)
example (a b : ℝ) (h : a < b) : a ≤ b := by
  exact le_of_lt h

-- Exercise 14)
example (a b c : ℝ) (h₁ : a ≤ b) (h₂ : b < c) : a < c := by
  exact lt_of_le_of_lt h₁ h₂

-- Exercise 15)
example (α : Type) (s t : Set α) : s ⊆ s ∪ t := by
  exact Set.subset_union_left

-- Exercise 16)
example (a b : ℝ) : |a + b| ≤ |a| + |b| := by
  exact abs_add_le a b

-- Exercise 17)
example (x : ℝ) : 0 < Real.exp x * (x ^ 2 + 1) := by
  apply mul_pos
  · exact Real.exp_pos x
  · exact add_pos_of_nonneg_of_pos (sq_nonneg x) one_pos

-- Exercise 18)
example (a b : ℝ) : (a + b) ^ 2 = a ^ 2 + 2 * a * b + b ^ 2 := by
  exact add_sq a b

-- Exercise 20)
example (f : ℝ → ℝ) (hf : Continuous f) (h0 : f 0 < 0) (h1 : 0 < f 1) :
    ∃ x, f x = 0 := by
  obtain ⟨x, -, hx⟩ :=
    intermediate_value_Icc zero_le_one hf.continuousOn ⟨h0.le, h1.le⟩
  exact ⟨x, hx⟩
