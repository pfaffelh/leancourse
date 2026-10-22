import Mathlib

/-!
# (witness) 1.1-c -- Arithmetic and induction on `Nat`

*Notes chapter 1.1, week 4.*
-/

open Nat

/-
In Mathlib, results on the natural numbers live in a `namespace` and
start with `Nat.???`. We do not want to type `Nat.` all the time,
which is what `open Nat` above is for.
-/

/-
We now come to natural numbers, and first look at how these are implemented in Lean. The corresponding definition is

inductive Nat
| zero : Nat
| succ (n : Nat) : Nat

This means that the type `Nat` (or `ℕ`) has the term `zero` (or `0`), and if `n : ℕ`, then `succ n : ℕ` (where `succ` stands for successor). A natural number is therefore either 0 or the successor of a natural number. You can also access this definition by: -/

#print Nat

-- Another hint that we will use often. Why don't you move the cursor to the `Nat` in the last line and press `F12`. You will then be guided to the definition of `Nat`.

-- The statement just made can also be proven (with cases')-/

example (n : ℕ) : n = 0 ∨ (∃ (k : ℕ), n = succ k) := by
  cases' n with k
  · left
    rfl
  · right
    use k

/- Note that a similar result is implemented in Mathlib: -/

example (n : ℕ) (hn : n ≠ 0) : ∃ (k : ℕ), n = succ k := by
  exact exists_eq_succ_of_ne_zero hn

/-
Exercise 1: Try to follow this example a little further.

Here I needed two lemmas (to apply `rw` to it; for the first one, lean knows that `α = ℕ` has the property `LT` (which stands for _less than_, i.e., `ℕ` is ordered)):-/

#check gt_iff_lt
#check Nat.succ_lt_succ_iff

/-
These and many more statements can also be found here, for example: https://leanprover-community.github.io/. See also below for further examples.-/

example (n : ℕ) (h : n > 1) : ∃ (k : ℕ), n = k + 2 := by
  rw [gt_iff_lt] at h
  have h' : n ≠ 0 := by exact Nat.ne_zero_of_lt h
  obtain ⟨i, hi⟩ := exists_eq_succ_of_ne_zero h'
  rw [hi, ← zero_add 1, Nat.succ_lt_succ_iff] at h
  obtain ⟨j, hj⟩ := exists_eq_succ_of_ne_zero h.ne.symm
  use j
  rw [hi, hj]

/-
  Now let's move on to some concrete calculations. We have already learned how `rw` works. This, together with the many statements in mathlib, will now help us solve arithmetic problems. We will first work in the set of natural numbers. The lemmas we will use in the following are, for example, the proofs stored in mathlib that ℕ has the properties `add_zero_class`, `mul_one_class`, `add_semigroup`, `add_comm_semigroup`, as well as the lemmas: (for the parentheses, see script)
-/

#check zero_add
#check add_zero
#check one_mul
#check mul_one
#check add_assoc
#check add_comm
#check mul_assoc
#check mul_comm

-- Here is an example: if you move the mouse over `add_zero`, vscode will show you the corresponding statement.
example (m n : ℕ) : m + n = n + m + 0 := by
  rw [add_zero, add_comm]

-- The `calc` mode is available to help you keep track of longer calculations. It works as follows in the example above:

example (m n : ℕ) : m + n = n + m + 0 := by
  calc m + n = n + m := by rw [add_comm]
    _ = n + m + 0 := by rw [add_zero]

/-
It is best to read the description of `calc` in the course notes.
In addition, we sometimes need the `nth_rw` tactic (see also the notes) when we want to specify where we want to rewrite something. See the next example.-/

lemma double (n : ℕ) : n + n = 2*n := by
  calc
  n + n = 1 * n + n := by nth_rw 1 [← one_mul n]
  _ = 1 * n + 1 * n := by nth_rw 2 [← one_mul n]
  _ = (1 + 1) * n := by rw [add_mul]
  _ = 2 * n := by rfl

/-
  Before we move on to the next tasks, let's prove a binomial formula: Note that each `by` functions as its own proof block.-/

lemma binom1 (n : ℕ) : (n+1)^2 = n^2 + 2*n + 1 :=
   calc (n+1)^2 = (n+1) * (n+1) := by rw [pow_two]
  _ = (n+1)*n + (n+1) * 1 := by rw [mul_add]
  _ = n*n + 1*n + (n+1) := by rw [add_mul, mul_one (n+1)]
  _ = n^2 + n + (n+1) := by rw [one_mul, ← pow_two]
  _ = n^2 + (n + n+1) := by rw [add_assoc, ← add_assoc n n 1]
  _ = n^2 + 2*n + 1 := by rw [← add_assoc, ← double]

/-
  Here is an alternative, but less readable proof:-/

example (n : ℕ): (n+1)^2 = n^2 + 2*n + 1 := by
  rw [pow_two, mul_add, add_mul, mul_one (n+1), one_mul, ← pow_two,  add_assoc, ← add_assoc n n 1, ← add_assoc, ← double]

/-
By the way: Rewriting every little calculation rule with rw can become tedious. There are four tactics that are much more powerful here:
- `ring`: knows all arithmetic rules in (semi) rings, e.g., natural numbers; however, it cannot use hypotheses; directly solves the binomial theorem;
- `norm_num`: can calculate with numbers (but not variables);
- `linarith`: can prove linear equations and inequalities with the help of hypotheses;
- `simp`: in Mathlib there are many lemmas that are intended to simplify things, such as `n + 0 = n`. These are always `=` or `↔` statements and are marked with @simp. The simp tactic can access these.-/

example (m n : ℕ) : (m + n)^3 = m^3 + 3*m*n^2 + 3*m^2*n + n^3 := by
  ring

example : 123 * 321 = 39483 := by
  norm_num

example (k m n : ℕ) (h1 : k ≤ m+n) (h2 : m < n) : k < 2*n := by
  linarith

-- For `simp`, note that there are versions `simp?`, which shows swhich lemmas were used, and `simp at h` applies the simplifications to the hypothesis `h`.
example (n : ℕ) : n + 0 + 0 = 0 + 0 + n := by
  simp

/-
  Here are a few tasks that can be solved with a single line of code:-/

-- Exercise 2a
example : 0 < 1 := by
  simp only [lt_one_iff, pos_of_gt]

-- Exercise 2b
example (n : ℕ): n * (n + 1) * (n + 2) = n^3 + 3 * n^2 + 2 * n := by
  ring

-- Exercise 2c
example : 1^100 = 100/100 := by
  norm_num

/-
  Exercise 3: a non-linear inequality; note that `calc` also works for inequalities, i.e.
  ```
  calc n = 1 * n := by sorry
   _ ≤ 2 * n := by sorry,
  ```
-/
example (n : ℕ) : n ≤ n^2 := by
  nlinarith

/-
  Now follow two tasks with less help. Part of each task is to find the corresponding result that makes the proof easier!

  Exercise 4:
-/

example (x y : ℕ): x^(y + 1) = x * x^y := by
  exact Nat.pow_succ'

example (m n : ℕ) : m^(n+2) = m * m^n * m := by
  rw [Nat.pow_succ', mul_comm, Nat.pow_succ']

/-
  Exercise 5:
-/

example (k m n : ℕ) (hkm : k ≤ m) (hmn : m ≤ n) : k^2 ≤ n^3 := by
  have h₀ : k^2 ≤ m^2 := by
    exact Nat.pow_le_pow_left hkm 2
  have h₁ : m^2 ≤ n^2 := by
    exact Nat.pow_le_pow_left hmn 2
  have h₂ : n^2 ≤ n^3 := by
    by_cases hn : n = 0
    · rw [hn]; rfl
    · have hn' : n > 0 := by exact zero_lt_of_ne_zero hn
      apply Nat.pow_le_pow_right hn' (by linarith)
  apply le_trans h₀ (le_trans h₁ h₂)

/-
  ## Induction

  Up to here we have calculated. The rest of this sheet is about
  complete induction, which is close to the `cases'` at the top: the
  same case distinction, but with the induction hypothesis in hand.
-/

/-- With complete induction, there is also the induction assumption, but the proof is identical: The syntax of the induction tactic is _induction n with d hd_, where n is an induction on n, the variable is renamed d, and hd is the induction hypothesis. -/

example (n : ℕ) : n = 0 ∨ (∃ (k : ℕ), n = succ k) := by
  induction n with
  | zero =>
    left
    rfl
  | succ n hn =>
    right
    use n

-- Exercise 1) Here is the first task. Remember that a hypothesis `h : P ∨ Q` can be resolved into two goals using `cases' h with hP hQ`. Alternatively you ocan use `rcases`.

example (n : ℕ) : (∃ (k : ℕ), n = 2 * k) ∨ (∃ (k : ℕ), n = 2 * k + 1) := by
  induction n with
  | zero =>
    left
    use 0
  | succ n hn =>
    cases' hn with hk hk
    · right
      obtain ⟨k, hk⟩ := hk
      use k
      rw [hk]
    · obtain ⟨k, hk⟩ := hk
      left
      use k + 1
      rw [hk]
      ring

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
  induction n with
  | zero =>
    simp
  | succ n hn =>
    rw [← not_iff_not] at *
    refine ⟨fun h' ↦ ?_, fun h' ↦ ?_⟩
    · push Not at *
      rw [pow_succ] at h'
      rw [← not_iff_not] at hn
      by_contra g
      have f := hn.2 g
      push Not at *
      have k : x ^ (n + 1) * x ≤ 1 := by
        apply mul_le_one₀ f h g
      linarith
    · rw [pow_succ]
      push Not at *
      apply one_lt_mul _ h'
      exact le_of_lt (hn.2 h')

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
  have h₁ : 0 = 0 * x^2 := by exact Eq.symm (zero_mul (x ^ 2))
  -- rw [h₁]
  apply mul_nonneg h₀
  exact sq_nonneg x

/-- Note that `ring` also works on `ℝ`: -/
example (x y : ℝ) : (x + y) ^ 2 = x ^ 2 + 2 * x * y + y ^ 2 := by
  ring

-- Exercise:
example (n : ℕ) (x : ℝ) (h : 0 ≤ x) : (1 : ℝ) + n * x ≤ (1 + x)^n := by
  induction n with
  | zero =>
    simp
  | succ n hn =>
    have hx1 : (1 : ℝ) ≤ 1 + x := by linarith
    have hpow : (1 : ℝ) ≤ (1 + x) ^ n := one_le_pow₀ hx1
    push_cast
    calc (1 : ℝ) + (↑n + 1) * x
        = (1 + ↑n * x) + x := by ring
      _ ≤ (1 + x) ^ n + x := by linarith
      _ ≤ (1 + x) ^ n + (1 + x) ^ n * x := by
            nlinarith [mul_le_mul_of_nonneg_right hpow h]
      _ = (1 + x) ^ (n + 1) := by ring
