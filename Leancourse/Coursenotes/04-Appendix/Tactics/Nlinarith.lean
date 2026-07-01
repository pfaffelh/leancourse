import Lean
import VersoManual
import Manual.Meta
import Leancourse.Misc.Defs
import Mathlib
open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open MyDef

set_option pp.rawOnError true

#doc (Manual) "`nlinarith`" =>
%%%
tag := "nlinarith"
%%%

*Summary:* `nlinarith` is the nonlinear extension of `linarith`.
Like `linarith`, it proves goals of the form `a ≤ b`, `a < b`,
`a = b`, or `False` from linear hypotheses over ordered fields.
Unlike `linarith`, it additionally multiplies pairs of hypotheses
to produce quadratic witnesses, so it can close many goals
involving products and squares.

*Examples:*

:::table (align := left) +header
* + Proof state
  + Tactic
  + New proof state
* + `x : ℝ` {br}[] ⊢ 0 ≤ x ^ 2 + 1
  + `nlinarith [sq_nonneg x]`
  + (no goals)
:::

*Remarks:*

* `nlinarith` is strictly more powerful than `linarith` but also
  slower; prefer `linarith` when possible.
* You can supply extra lemmas as hints:
  `nlinarith [sq_nonneg x, mul_self_nonneg y]`. Hints of the form
  `0 ≤ ...` are especially useful.
* For purely polynomial identities (not inequalities), use `ring`
  or `polyrith` instead.



::::keepEnv
:::example " "
```lean
example (x : ℝ) : 0 ≤ x ^ 2 + 1 := by
  nlinarith [sq_nonneg x]

example (a b : ℝ) (h : 0 ≤ a) (h' : 0 ≤ b) : 0 ≤ a * b := by
  nlinarith
```

:::
::::
