import Mathlib

/-
# Exercise Sheet 7b: The `conv` tactic

`conv` (conversion mode) lets you rewrite a *specific* subterm instead
of the first match, and reach *under* binders where plain `rw` fails.

Inside `conv => …`:
* `lhs` / `rhs` pick a side of `=` / `↔` / a binary operation,
* `enter [i, j, …]` descends into arguments,
* `ext x` goes under a binder,

and then `rw` / `simp` acts only on the focused subterm. The shorthands
`conv_lhs => …` / `conv_rhs => …` start focused on one side, and
`conv at h => …` works inside a hypothesis.

Replace each `sorry` with a proof that uses `conv`.
-/

-- 1. Plain `rw [h]` would rewrite BOTH `a`s. Rewrite only the first,
--    so the goal becomes `b + a = b + a`.
example (a b : ℕ) (h : a = b) : a + a = b + a := by
  sorry

-- 2. Rewrite only the SECOND `a`, turning the goal into `a + b = a + b`.
example (a b : ℕ) (h : a = b) : a + a = a + b := by
  sorry

-- 3. Rewrite under the `λ`-binder (plain `rw` cannot reach there).
example (f : ℕ → ℕ) (h : ∀ n, f n = 0) :
    (fun n => f n + 1) = (fun n => 0 + 1) := by
  sorry

-- 4. Use `conv at h` to simplify the hypothesis to `a = b`, then finish.
example (a b : ℕ) (h : a + 0 = b) : a = b := by
  sorry

-- 5. Reach the first `a` deep inside with `enter`.
example (a b : ℕ) (h : a = b) :
    (a + 1) + (a + 2) = (b + 1) + (a + 2) := by
  sorry
