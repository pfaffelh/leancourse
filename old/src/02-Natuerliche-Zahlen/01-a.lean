import tactic -- lade lean-Taktiken
import data.real.basic
open nat

open_locale big_operators

/-
  a) Rechnen mit calc; (n-1)(n+1) = n^2-1
  b) Induktion: einfache Beispiele Gauß
  c) Teilbarkeiten: Beginn mit is_even  
-/

-- Dies sind Namen für alle verwendeten Aussagen
variables (P Q R S T: Prop) 

theorem forall_practice1 (f : ℕ → ℕ)
(h : ∀ (a : ℕ), f(a) + f(a + 1) = f(a + 2)) :
∀ (m : ℕ), 2 * f(m + 2) = f(m) + f(m + 3) :=
begin
  intro m, 
  rw ← h (m+1), 
  rw ← add_assoc, 
  rw h m, 
  ring,
end

-- intro ring, linarith, norm_num, simp

example (x : ℕ) : (x < 5) ↔ (2 * x < 10) :=
begin
  split;
  { intro h, linarith, },
end

def my_even (n : ℤ) := ∃ (m : ℤ), n = 2 * m

example : my_even 10 :=
begin
  use 5, norm_num,
end
 
example (n : ℤ) (h : my_even n) : (my_even (4 * n)) :=
begin
  cases h with x hx, rw hx, use (4 * x), ring, 
end
 
theorem even2 :
∃ (a : ℤ), ∀ (b : ℤ), my_even (a * b) :=
begin
  use 2, intro b, use b,
end

example : ¬(∀ (x : ℕ), x + 2 = 5) :=
begin
  push_neg,
  use 0, linarith,
end

example : ¬(∃ (x : ℕ), ∀ (y : ℕ), x * y = x + y) :=
begin
  push_neg,
  intro x, 
  use 1, 
  linarith,
end

/-
```
inductive nat
| zero : nat
| succ (n : nat) : nat


notation `ℕ` := nat
```
-/

example (k m : ℕ) : (k + m + 0 = m + k + 0) :=
begin
  rw [add_zero, add_zero, add_comm],
end

example (m n : ℕ) (h : m = n): 0 + n = 0 + 0 + m:= 
 begin
  nth_rewrite 2 zero_add, rw h,
 end



example (S T : set ℕ) (x : ℕ) (h : S ⊆ T) :  (x ∈ S) → (x ∈ T) :=
begin
  convert h, simp, exact iff_of_true (h x) h,
end

variables n : ℕ

example : n+1 = 1+n :=
begin
  rw add_comm, 
end

example : 0<1 :=
begin
  exact zero_lt_one,
end

example : n>0 → ∃ k : ℕ, n = k+1 :=
begin
  cases n, intro h, cases h, intro x, use n, 
end

example : ∃ k l: ℕ, k*l=16 :=
begin
  use [8,2], ring, 
end

example (m n : ℕ) : (m+1)+n = (m+n)+1 :=
begin
  ring, 
end

example (n : ℕ): (n+1)^2 = n^2 + 2*n + 1 :=
begin
  have h : n + n = 2*n, 
  {
    nth_rewrite 0 ← one_mul n,
    nth_rewrite 1 ← one_mul n,
    rw ← add_mul,
  },
  calc (n+1)^2 = (n+1) * (n+1) : by { rw pow_two, }
  ... = (n+1)*n + (n+1) * 1: by {rw mul_add, }
  ... = n*n + 1*n + (n+1) : by {rw add_mul, rw mul_one (n+1),}
  ... = n^2 + n + (n+1) : by {rw one_mul, rw ← pow_two,}
  ... = n^2 + (n + n+1) : by {rw add_assoc, rw ← add_assoc n n 1,}
  ... = n^2 + 2*n + 1 : by { rw ← add_assoc, rw ← h, },
end

example (n : ℕ): (n+1)^2 = n^2 + 2*n + 1 :=
begin
  have h : n + n = 2*n, by { nth_rewrite 0 ← one_mul n,  nth_rewrite 1 ← one_mul n, rw ← add_mul, },
  rw [pow_two, mul_add, add_mul, mul_one (n+1), one_mul, ← pow_two,  add_assoc, ← add_assoc n n 1, ← add_assoc, ← h],
end

example (n : ℕ) : n + n = 2*n :=
begin
  calc n + n = 1 * n + 1 * n : by {nth_rewrite 0 ← one_mul n,
    nth_rewrite 1 ← one_mul n,}
  ... = (1 + 1) * n : by {rw add_mul, }
  ... = 2 * n : by {refl, }
end


def is_even (n : ℕ) := ∃ (k : ℕ), n = 2*k

def double (n : ℕ) := 2*n

example : is_even n ↔ ¬(is_even (n+1)) :=
begin
  sorry, 
end

example : ∀ (k : ℕ), is_even (2*k) :=
begin
  sorry, 
end

example (m n : ℕ) : (m+1)^n = m^n * m :=
begin
  sorry,
end

example : ∑ i ≤ 4, i ^ 2 = 30 :=
begin
  refl,
end

lemma choose_succ : ∀ k n : ℕ, k ≥ 1 → choose (n+1) k = choose n k  + choose n (k-1) :=
begin
  intros k n h,
  cases k,
  linarith,
  rw succ_sub_one, 
  rw choose_succ_succ, rw add_comm, 
end

example (s : finset ℕ) (f : ℕ → ℝ ) (g :  ℕ → ℝ ) : s.sum (λ (x : ℕ), f x) + s.sum (λ (x : ℕ), g x) = s.sum (λ (x : ℕ), f x + g x)
-- ∑ x in s, f x + ∑ x in s, g x = ∑ x in s, (f x + g x) 
:=
begin
  rw finset.sum_add_distrib,
end

example (n : ℕ) :
  ∑ i in range n, (i+1 : ℝ) = ∑ i in range ( n+1 ), (i : ℝ)  :=
begin
  sorry,
end

example (n : ℕ) :
  ∑ i in range (n + 1), nat.choose n i = 2 ^ n  :=
begin
  sorry,
end


lemma sum_fifths (n : ℕ) : ∑ i in range n, (i : ℚ)^5 = (4*(n*(n-1)/2)^3-(n*(n-1)/2)^2)/3 :=
begin
  induction n with d hd,
  { simp, },
  { rw [finset.sum_range_succ, hd],
    simp,
    ring }
end

example (n i : ℕ) :
  (nat.choose (n+1) (i+1)) = (nat.choose n i) + (nat.choose n (i + 1)) :=
begin
  exact nat.choose_succ_succ n i,
end

example (x y : ℕ) (n : ℕ) :
  ∑ i in range (n+1), (nat.choose n i) * (x^i) * (y^(n-i)) = (x + y)^n :=
begin
--  induction n with d hd,
--  simp,
--  rw d.choose_succ_succ,
  sorry,
end

example (n : ℕ) :
  ∑ i in range n, (i : ℝ) = n * (n - 1) / 2 :=
begin
  induction n with d hd,
  { -- base case: sum over empty type is 0 * (0 - 1) / 2
    simp },
  { -- inductive step
    rw [sum_range_succ, hd],
    simp, -- tidies up and reduces the goal to
    -- ⊢ ↑d * (↑d - 1) / 2 + ↑d = (↑d + 1) * ↑d / 2
    ring, -- a more appropriate tactic to finish the job
  }
end

lemma choose_succ : ∀ k n : ℕ, k ≥ 1 → choose (n+1) k = choose n k  + choose n (k-1) :=
begin
  intros k n h,
  cases k,
  linarith,
  rw succ_sub_one, 
  rw choose_succ_succ, rw add_comm, 
end

example (s : finset ℕ) (f : ℕ → ℝ ) (g :  ℕ → ℝ ) : s.sum (λ (x : ℕ), f x) + s.sum (λ (x : ℕ), g x) = s.sum (λ (x : ℕ), f x + g x)
-- ∑ x in s, f x + ∑ x in s, g x = ∑ x in s, (f x + g x) 
:=
begin
  rw finset.sum_add_distrib,
end






