import tactic -- lade lean-Taktiken
open nat

/-
inductive nat
| zero : nat
| succ (n : nat) : nat
-/

variables n : ℕ



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

