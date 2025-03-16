import tactic
import data.real.basic
import data.nat.choose.basic
-- import tactic.linarith
import algebra.big_operators.ring
-- import algebra.big_operators.intervals
-- import algebra.big_operators.order
-- import algebra.big_operators.nat_antidiagonal

open nat
open finset

open_locale big_operators

theorem vandermonde : ∀ (n m r : ℕ), choose (m+n) r = ∑ k in range (r + 1), (choose m k) * (choose n (r-k)) :=
begin  
  intro n,
  induction n with d hd,
  {
    intros m r,
    rw sum_range_succ, simp, 
    have h1 : ∀ i : ℕ, i ∈ range (r) → ((choose m i) * (choose 0 (r-i)) = 0),
    intros i h, 
    simp, right, rw choose_eq_zero_iff, simp, 
    exact mem_range.mp h, 
    exact sum_eq_zero h1,
  },
  {
    intros m r,
    specialize hd m,
    have hd' := hd,
    cases r,
    { simp, },
    specialize hd r,
    specialize hd' (r+1),
    rw succ_add at *,
    rw add_succ at *,
    simp at *,
    rw choose_succ_succ,
    rw hd, rw hd',  
    nth_rewrite 1 sum_range_succ,
    nth_rewrite 2 sum_range_succ,
    simp,
    rw ← add_assoc, 
    rw (add_left_inj (m.choose r.succ)),
    rw ← finset.sum_add_distrib,
    rw finset.sum_congr,
    refl,
    intros x h,
    rw succ_sub,
    rw choose_succ_succ,
    rw mul_add, 
    apply nat.le_of_lt_succ (mem_range.mp h),
  }
end

theorem add_pow {x y : ℝ} (n : ℕ) :
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



