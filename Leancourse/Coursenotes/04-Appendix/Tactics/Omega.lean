import Lean
import VersoManual
import Manual.Meta
import Leancourse.Misc.Defs
import Mathlib
open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open MyDef

set_option pp.rawOnError true

#doc (Manual) "`omega`" =>
%%%
tag := "omega"
%%%

*Summary:* `omega` is a decision procedure for linear arithmetic
over the integers `ℤ` and the natural numbers `ℕ`. It closes goals
involving `+`, `-`, `*` (by a constant), `/`, `%`, `≤`, `<`, `=`,
`≠`, `∧`, `∨`, and `¬`, provided the goal reduces to a Presburger
arithmetic statement. It is one of the most useful tactics for
closing routine numerical side conditions.

*Examples:*

:::table (align := left) +header
* + Proof state
  + Tactic
  + New proof state
* + `a b : ℕ` {br}`h : a ≤ b` {br}[] ⊢ a ≤ b + 1
  + `omega`
  + (no goals)
* + `n : ℕ` {br}`h : n ≠ 0` {br}[] ⊢ 0 < n
  + `omega`
  + (no goals)
:::

*Remarks:*

* `omega` is complete for linear arithmetic: if the goal is a true
  statement in Presburger arithmetic, `omega` will close it.
* It does **not** handle nonlinear products (use `nlinarith`) or
  real-valued arithmetic (use `linarith`).
* It works equally well on `ℤ` and `ℕ`, automatically handling the
  fact that natural numbers are nonnegative.



::::keepEnv
:::example " "
```lean
example (a b : ℕ) (h : a ≤ b) : a ≤ b + 1 := by
  omega

example (n : ℕ) (h : n ≠ 0) : 0 < n := by
  omega

example (x y : ℤ) (h₁ : x + y = 5) (h₂ : x - y = 1) : x = 3 := by
  omega
```

:::
::::
