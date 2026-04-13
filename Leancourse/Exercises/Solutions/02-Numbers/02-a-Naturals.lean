import Mathlib

open Nat

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
  have h' : n ≠ 0 := by exact not_eq_zero_of_lt h
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
    exact pow_le_pow_of_le_left hkm 2
  have h₁ : m^2 ≤ n^2 := by
    exact pow_le_pow_of_le_left hmn 2
  have h₂ : n^2 ≤ n^3 := by
    by_cases hn : n = 0
    · rw [hn]; rfl
    · have hn' : n > 0 := by exact zero_lt_of_ne_zero hn
      apply pow_le_pow_of_le_right hn' (by linarith)
  apply le_trans h₀ (le_trans h₁ h₂)
