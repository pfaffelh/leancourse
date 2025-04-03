import Mathlib

open Nat

open_locale big_operators

/-
  a) Rechnen mit calc; (n-1)(n+1) = n^2-1
  b) Induktion: einfache Beispiele Gauß
  c) Teilbarkeiten: Beginn mit is_even
-/

-- Dies sind Namen für alle verwendeten Aussagen
variable (P Q R S T: Prop)

theorem forall_practice1 (f : ℕ → ℕ)
(h : ∀ (a : ℕ), f a  + f (a + 1) = f (a + 2)) :
∀ (m : ℕ), 2 * f (m + 2) = f (m) + f (m + 3) := by
  intro m
  rw [← h (m+1)]
  rw [← add_assoc]
  rw [h m]
  ring

-- intro ring, linarith, norm_num, simp

example (x : ℕ) : (x < 5) ↔ (2 * x < 10) := by
  constructor
  · intro h
    linarith
  · intro h
    linarith

def My_Even (n : ℤ) := ∃ (m : ℤ), n = 2 * m

example : My_Even 10 := by
  use 5
  norm_num

example (n : ℤ) (h : My_Even n) : (My_Even (4 * n)) := by
  cases' h with x hx
  rw [hx]
  use (4 * x)
  ring

theorem Even2 :
∃ (a : ℤ), ∀ (b : ℤ), My_Even (a * b) := by
  use 2
  intro b
  use b

example : ¬(∀ (x : ℕ), x + 2 = 5) := by
  push_neg
  use 0
  linarith

example : ¬(∃ (x : ℕ), ∀ (y : ℕ), x * y = x + y) := by
  push_neg
  intro x
  use 1
  linarith

/-
```
inductive nat
| zero : nat
| succ (n : nat) : nat


notation `ℕ` := nat
```
-/

example (k m : ℕ) : (k + m + 0 = m + k + 0) := by
  rw [add_zero, add_zero, add_comm]

example (m n : ℕ) (h : m = n): 0 + n = 0 + 0 + m := by
  nth_rewrite 2 [zero_add]
  rw [h]

example (S T : Set ℕ) (x : ℕ) (h : S ⊆ T) :  (x ∈ S) → (x ∈ T) := by
  intro h₁
  exact h h₁

variable (n : ℕ)

example : n + 1 = 1 + n := by
  rw [add_comm]

example : 0 < 1 := by
  exact zero_lt_one

example : n>0 → ∃ k : ℕ, n = k+1 := by
  cases' n with k hk
  · intro h
    cases' h
  · intro x
    use k

example : ∃ k l: ℕ, k * l = 16 := by
  use 8, 2

example (m n : ℕ) : (m+1)+n = (m+n)+1 := by
  ring

example (n : ℕ): (n+1)^2 = n^2 + 2*n + 1 := by
  have h : n + n = 2*n := by
    nth_rewrite 1 [← one_mul n]
    nth_rewrite 2 [← one_mul n]
    rw [← add_mul]
    rfl
  calc (n+1)^2 = (n+1) * (n+1) := by rw [pow_two]
  _ = (n+1)*n + (n+1) * 1 := by rw [mul_add]
  _ = n*n + 1*n + (n+1) := by rw [add_mul, mul_one (n+1)]
  _ = n^2 + n + (n+1) := by rw [one_mul, ← pow_two]
  _ = n^2 + (n + n+1) := by rw [add_assoc, ← add_assoc n n 1]
  _ = n^2 + 2*n + 1 := by rw [← add_assoc, ← h]


example (n : ℕ): (n+1)^2 = n^2 + 2*n + 1 := by
  have h : n + n = 2*n := by
    nth_rewrite 1 [← one_mul n]
    nth_rewrite 2 [← one_mul n]
    rw [← add_mul]
    rfl
  rw [pow_two, mul_add, add_mul, mul_one (n+1), one_mul, ← pow_two,  add_assoc, ← add_assoc n n 1, ← add_assoc, ← h]

example (n : ℕ) : n + n = 2*n := by
  calc n + n = 1 * n + 1 * n := by
      nth_rewrite 1 [← one_mul n]
      nth_rewrite 2 [← one_mul n]
  _ = (1 + 1) * n := by rw [add_mul]
  _ = 2 * n := by rfl


def Is_Even (n : ℕ) := ∃ (k : ℕ), n = 2*k

def double (n : ℕ) := 2*n

example : Is_Even n ↔ ¬(Is_Even (n+1)) := by
  sorry

example : ∀ (k : ℕ), Is_Even (2*k) := by
  sorry

example (m n : ℕ) : (m+1)^n = m^n * m := by
  sorry

example : ∑ i ≤ 4, i ^ 2 = 30 := by
  rfl

lemma choose_succ : ∀ k n : ℕ, k ≥ 1 → choose (n+1) k = choose n k  + choose n (k-1) := by
  intro k n h
  cases' k
  linarith
  rw [succ_sub_one]
  rw [choose_succ_succ, add_comm]

example (s : Finset ℕ) (f : ℕ → ℝ ) (g :  ℕ → ℝ ) : s.sum (fun (x : ℕ) ↦ f x) + s.sum (fun  (x : ℕ) ↦ g x) = s.sum (fun (x : ℕ) ↦ f x + g x)
-- ∑ x in s, f x + ∑ x in s, g x = ∑ x in s, (f x + g x)
:= by
  rw [← Finset.sum_add_distrib]

example (n : ℕ) :
  ∑ (i ≤ n), i + 1  = ∑ (i ≤ n+1), i := by
    sorry

open Nat

example (n : ℕ) :
  ∑ i ≤ n, choose n i = 2 ^ n  := by
    sorry

example (n i : ℕ) :
  (choose (n+1) (i+1)) = (choose n i) + (choose n (i + 1)) := by
    exact choose_succ_succ n i

example (x y : ℕ) (n : ℕ) :
  ∑ i ≤ n, (choose n i) * (x^i) * (y^(n-i)) = (x + y)^n := by
  --  induction n with d hd,
  --  simp,
  --  rw d.choose_succ_succ,
  sorry

example (n : ℕ) :
  ∑ i < n, i = n * (n - 1) / 2 := by
  induction n
  · simp only [_root_.zero_le, Nat.sub_eq_zero_of_le, mul_zero, Nat.zero_div,
    Finset.sum_eq_zero_iff, Finset.mem_Iio, not_lt_zero', IsEmpty.forall_iff, implies_true]
  · sorry

lemma choose_succ : ∀ k n : ℕ, k ≥ 1 → choose (n+1) k = choose n k  + choose n (k-1) :=
begin
  intros k n h,
  cases k,
  linarith,
  rw succ_sub_one,
  rw choose_succ_succ, rw add_comm,
end
