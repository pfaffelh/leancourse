import Mathlib

open Nat

/-- In Mathlib, there are many results on natural numbers. All such results are organized into `namespace`s, i.e. results on the natural numbers start with `Nat.???`. We do not want to type `Nat.` all the time, which can be done using `open Nat`.-/

/-
  We now come to complete induction. This is actually similar to cases'.-/

example (n : ℕ) : n = 0 ∨ (∃ (k : ℕ), n = succ k) := by
  cases' n with k
  · left
    rfl
  · right
    use k

/-- With complete induction, there is also the induction assumption, but the proof is identical: The syntax of the induction tactic is _induction n with d hd_, where n is an induction on n, the variable is renamed d, and hd is the induction hypothesis. -/

example (n : ℕ) : n = 0 ∨ (∃ (k : ℕ), n = succ k) := by
  induction n with
  | zero =>
    left
    rfl
  | succ n hn =>
    right
    use n

-- Exercise 1) Here is the first task. Remember that a hypothesis `h : P ∨ Q` can be resolved into two goals using `cases' h with hP hQ`. Alternatively you can use `rcases`.

example (n : ℕ) : (∃ (k : ℕ), n = 2 * k) ∨ (∃ (k : ℕ), n = 2 * k + 1) := by
  induction n with
  | zero =>
    sorry
  | succ n hn =>
    sorry

-- Exercise 2: A non-negative real number `x` has `x ≤ 1` if `x^n ≤ 1`. This can be proven by induction.
/-
  You will probably need the following in the proof:-/

#check pow_succ
#check not_iff_not
#check one_lt_mul
#check le_of_lt
#check pow_nonneg
#check mul_le_one₀

example (x : ℝ) (n : ℕ) (h : 0 ≤ x) : x^(n+1) ≤ 1 ↔ x ≤ 1 := by
  refine pow_le_one_iff_of_nonneg h ?_
  exact Ne.symm (zero_ne_add_one n)

example (x : ℝ) (n : ℕ) (h : 0 ≤ x) : x^(n+1) ≤ 1 ↔ x ≤ 1 := by
  sorry

-- Exercise 3: Here is a problem from Calculus 1: `1 + n * x ≤ (1 + x)^n`. This applies if `-1 ≤ x`. If this is too difficult, change the assumption `h` to `0 ≤ x`.
-- Here are a few statements that may be helpful (go to the end of each line to see the statement on the right):

#check @ add_mul
#check @ add_assoc
#check @ mul_le_mul_of_nonneg_left
#check @ mul_nonneg
#check @ Nat.mul_le_mul_left
#check @ le_trans

-- Note that in the next exercise we must transform `d : ℕ` to `d : ℝ`. Lean does this using a function `ℕ → ℝ`, which one usually does not talk about in mathematics. Lean displays `d : ℝ` by `↑d`.
example (x : ℝ) (d : ℕ) : 0 ≤ (d : ℝ) * x^2 := by
  have h₀ : 0 ≤ (d : ℝ):= by exact cast_nonneg' d
  sorry

/-- Note that `ring` also works on `ℝ`: -/
example (x y : ℝ) : (x + y) ^ 2 = x ^ 2 + 2 * x * y + y ^ 2 := by
  ring

-- Exercise 4:
example (n : ℕ) (x : ℝ) (h : 0 ≤ x) : (1 : ℝ) + n * x ≤ (1 + x)^n := by
  sorry
