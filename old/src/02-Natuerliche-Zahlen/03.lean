import tactic
import data.real.basic
import data.nat.choose.basic
import algebra.big_operators.ring
import data.polynomial.coeff

open_locale big_operators

open nat
open finset
open polynomial finset.nat

/- Here is an adapted statement and proof in mathlib (by Chris Hughes, for commuting elements in non-commutative semirings)
  -/

theorem add_pow_mathlib {x y : ℝ} (n : ℕ) :
  (x + y) ^ n = ∑ m in range (n + 1), x ^ m * y ^ (n - m) * choose n m :=
begin
  have h : commute x y, exact commute.all x y,
  let t : ℕ → ℕ → ℝ := λ n m, x ^ m * (y ^ (n - m)) * (choose n m),
  change (x + y) ^ n = ∑ m in range (n + 1), t n m,
  have h_first : ∀ n, t n 0 = y ^ n,
  {
    intro n, dsimp [t], simp,
  },
  have h_last : ∀ n, t n n.succ = 0,
  {
    intro n, dsimp [t], simp,
  },
  have h_middle : ∀ (n i : ℕ), (i ∈ range n.succ) →
   ((t n.succ) ∘ nat.succ) i = x * (t n i) + y * (t n i.succ),
   {
    intros n i h_mem,
    have h_le : i ≤ n,
    {
      apply nat.le_of_lt_succ (mem_range.mp h_mem),
    },
    dsimp [t], -- simp,
    rw choose_succ_succ,
    rw nat.cast_add,
    rw mul_add,
    congr' 1,
    { 
      rw pow_succ x,
      simp, rw mul_assoc, rw mul_assoc, rw mul_assoc, 
    },
    { 
    rw [← mul_assoc y, ← mul_assoc y], 
--    simp,

-- pow_succ a n : a^(n+1) = a * a^n
-- choose_succ_self n : choose n n+1 = 0
    rw [(h.symm.pow_right i.succ).eq],
    by_cases h_eq : i = n,
      { rw [h_eq, choose_succ_self, nat.cast_zero, mul_zero, mul_zero] },
      { rw [succ_sub (lt_of_le_of_ne h_le h_eq)],
        rw [pow_succ y, mul_assoc, mul_assoc, mul_assoc, mul_assoc] } }
  },
  induction n with n ih,
  -- sum_range_succ
  { rw [pow_zero, sum_range_succ, range_zero, sum_empty, zero_add],
    dsimp [t], rw [pow_zero, pow_zero, choose_self, nat.cast_one, mul_one, mul_one] },
  { rw [sum_range_succ', h_first],
    rw [sum_congr rfl (h_middle n), sum_add_distrib, add_assoc],
    rw [pow_succ (x + y), ih, add_mul, mul_sum, mul_sum],
    congr' 1,
    rw [sum_range_succ', sum_range_succ, h_first, h_last,
       mul_zero, add_zero, pow_succ] }
end

/-- Here I adapt the proof of Vandermonde's identity. -/
example {x y : ℝ} (n : ℕ) :
  (x + y) ^ n = ∑ (ij : ℕ × ℕ) in antidiagonal n, x ^ ij.1 * y ^ ij.2 * choose n ij.1 := 
  --(m n k : ℕ) : (m + n).choose k = ∑ (ij : ℕ × ℕ) in antidiagonal k, m.choose ij.1 * n.choose ij.2 :=
begin
  have h : (X + C y) ^ n = ∑ (ij : ℕ × ℕ) in antidiagonal n, X ^ ij.1 * (C y) ^ ij.2 * choose n ij.1,
  {
    rw ← coeff_inj ((X + C y) ^ n) = (∑ (ij : ℕ × ℕ) in antidiagonal n, X ^ ij.1 * (C y) ^ ij.2 * choose n ij.1),

    sorry,
  },




  have h : (x/y + 1) ^ n = ∑ (i : ℕ) in range (n + 1), (x/y) ^ i * ↑(n.choose i),
--  rw coeff_X_add_one_pow, 


--  calc (m + n).choose k
--      = ((X + 1) ^ (m + n)).coeff k : _
--  ... = ((X + 1) ^ m * (X + 1) ^ n).coeff k : by rw pow_add
--  ... = ∑ (ij : ℕ × ℕ) in antidiagonal k, m.choose ij.1 * n.choose ij.2 : _,
--  { rw [coeff_X_add_one_pow, nat.cast_id], },
--  { rw [coeff_mul, finset.sum_congr rfl],
--    simp only [coeff_X_add_one_pow, nat.cast_id, eq_self_iff_true, imp_true_iff], }
end

#check eq_self_iff_true 

#check coeff_X_add_one_pow

#check@ coeff_inj 
