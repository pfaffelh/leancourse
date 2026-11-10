import Mathlib

/-!
# (witness) 1.1-c -- Arithmetic and induction on `ℕ`

*Notes chapter 1.1, week 4.*
-/

open Nat

/-! ## Part 1: Cases on `ℕ` -/

-- Exercise 1)
example (n : ℕ) (h : n > 1) : ∃ k : ℕ, n = k + 2 := by
  use n - 2
  omega

/-! ## Part 2: Finding a lemma -/

-- Exercise 2)
example (a : ℕ) : 0 + a = a :=
  zero_add a

-- Exercise 3)
example (a b c : ℕ) : (a + b) * c = a * c + b * c :=
  add_mul a b c

-- Exercise 4)
example (a b c : ℕ) : a + b + c = a + (b + c) :=
  add_assoc a b c

-- Exercise 5)
example (a : ℕ) : a ^ 2 = a * a :=
  pow_two a

/-! ## Part 3: Rewriting and `calc` -/

lemma double (n : ℕ) : n + n = 2 * n := by
  calc n + n = 1 * n + n := by nth_rw 1 [← one_mul n]
    _ = 1 * n + 1 * n := by nth_rw 2 [← one_mul n]
    _ = (1 + 1) * n := by rw [add_mul]
    _ = 2 * n := by rfl

-- Exercise 6)
example (a b c : ℕ) : (a + b) * c = c * a + b * c := by
  rw [add_mul, mul_comm a c]

-- Exercise 7)
example (m n : ℕ) : m * (n + 1) + 0 = m + m * n := by
  calc m * (n + 1) + 0 = m * (n + 1) := by rw [add_zero]
    _ = m * n + m * 1 := by rw [mul_add]
    _ = m * n + m := by rw [mul_one]
    _ = m + m * n := by rw [add_comm]

/-! ## Part 4: Four automatic tactics -/

-- Exercise 8)
example : 0 < 1 := by
  norm_num

-- Exercise 9)
example (n : ℕ) : n * (n + 1) * (n + 2) = n ^ 3 + 3 * n ^ 2 + 2 * n := by
  ring

-- Exercise 10)
example : 1 ^ 100 = 100 / 100 := by
  norm_num

-- Exercise 11)
example (k m n : ℕ) (h₁ : k + 2 ≤ m) (h₂ : m < n) : k + 3 ≤ n := by
  linarith

-- Exercise 12)
example (n : ℕ) : 0 * n + n * 1 + 0 = n := by
  simp

/-! ## Part 5: Lemmas in proofs -/

-- Exercise 13)
example (m n : ℕ) : m ^ (n + 2) = m * m ^ n * m := by
  rw [Nat.pow_succ', mul_comm, Nat.pow_succ']

-- Exercise 14)
example (n : ℕ) : n ≤ n ^ 2 := by
  exact Nat.le_self_pow (by norm_num) n

-- Exercise 15)
example (k m n : ℕ) (hkm : k ≤ m) (hmn : m ≤ n) : k ^ 2 ≤ n ^ 3 := by
  have h₀ : k ^ 2 ≤ m ^ 2 := Nat.pow_le_pow_left hkm 2
  have h₁ : m ^ 2 ≤ n ^ 2 := Nat.pow_le_pow_left hmn 2
  have h₂ : n ^ 2 ≤ n ^ 3 := by
    by_cases hn : n = 0
    · rw [hn]; rfl
    · exact Nat.pow_le_pow_right (Nat.pos_of_ne_zero hn) (by norm_num)
  exact le_trans h₀ (le_trans h₁ h₂)

-- Exercise 16)
example (x : ℝ) (n : ℕ) (h : 0 ≤ x) : x ^ (n + 1) ≤ 1 ↔ x ≤ 1 := by
  constructor
  · intro h₁
    by_contra g
    push Not at g
    have : 1 < x ^ (n + 1) := one_lt_pow₀ g (by omega)
    linarith
  · intro hx
    exact pow_le_one₀ h hx

/-! ## Part 6: Induction -/

-- Exercise 17)
example (n : ℕ) : (∃ k : ℕ, n = 2 * k) ∨ (∃ k : ℕ, n = 2 * k + 1) := by
  induction n with
  | zero =>
    left
    use 0
  | succ n hn =>
    obtain (hk | hk) := hn
    · right
      obtain ⟨k, hk⟩ := hk
      use k
      rw [hk]
    · obtain ⟨k, hk⟩ := hk
      left
      use k + 1
      rw [hk]
      ring

-- Exercise 18)
example (n : ℕ) (x : ℝ) (h : 0 ≤ x) : (1 : ℝ) + n * x ≤ (1 + x) ^ n := by
  induction n with
  | zero =>
    simp
  | succ n hn =>
    have hpow : (1 : ℝ) ≤ (1 + x) ^ n := one_le_pow₀ (by linarith)
    have hmul : x ≤ (1 + x) ^ n * x := by
      calc x = 1 * x := by rw [one_mul]
        _ ≤ (1 + x) ^ n * x := mul_le_mul_of_nonneg_right hpow h
    push_cast
    calc (1 : ℝ) + (n + 1) * x = (1 + n * x) + x := by ring
      _ ≤ (1 + x) ^ n + (1 + x) ^ n * x := by linarith
      _ = (1 + x) ^ (n + 1) := by ring

-- Exercise 19)
example (n : ℕ) : n + 1 ≤ 2 ^ n := by
  induction n with
  | zero =>
    simp
  | succ n hn =>
    rw [pow_succ]
    linarith

/-! ## Part 7: Sums -/

-- Exercise 20)
example (n : ℕ) : 2 * (∑ k ∈ Finset.range (n + 1), k) = n * (n + 1) := by
  induction n with
  | zero =>
    simp
  | succ n hn =>
    rw [Finset.sum_range_succ, mul_add, hn]
    ring

-- Exercise 21)
example (n : ℕ) :
    (∑ k ∈ Finset.range n, (2 * k + 1)) = n ^ 2 := by
  induction n with
  | zero =>
    simp
  | succ n hn =>
    rw [Finset.sum_range_succ, hn]
    ring

/-! ## Part 8: `omega` -/

-- Exercise 22)
example (n : ℕ) : ∃ q r : ℕ, n = 2 * q + r ∧ r < 2 := by
  use n / 2, n % 2
  omega

-- Exercise 23)
example (n : ℕ) (h : 0 < n) : n - 1 < n := by
  omega
