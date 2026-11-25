import Mathlib

/-
# A-b -- `conv`

*Appendix, week 12.*

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

## Introduced here

| tactic                    | use it when                               |
|---------------------------|-------------------------------------------|
| `conv => …`               | rewrite one chosen subterm of the goal    |
| `conv_lhs`, `conv_rhs`    | the same, starting on one side of `=`     |
| `conv at h => …`          | the same inside the hypothesis `h`        |
| `lhs`, `rhs`, `enter [i]` | inside `conv`: move to a subterm          |

## Tactics from earlier sheets

| sheet   | tactics |
|---------|---------|
| `L-a`   | `exact` |
| `1.1-a` | `rw`    |
| `1.5-a` | `ext`   |
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
--    (`exact h` alone fails: `0 + a` does not reduce to `a`.)
example (a b : ℕ) (h : 0 + a = b) : a = b := by
  sorry

-- 5. Reach the first `a` deep inside with `enter`.
example (a b : ℕ) (h : a = b) :
    (a + 1) + (a + 2) = (b + 1) + (a + 2) := by
  sorry
