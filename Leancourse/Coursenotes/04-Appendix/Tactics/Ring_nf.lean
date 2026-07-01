import Lean
import VersoManual
import Manual.Meta
import Leancourse.Misc.Defs
import Mathlib
open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open MyDef

set_option pp.rawOnError true

#doc (Manual) "`ring_nf`" =>
%%%
tag := "ring-nf"
%%%

*Summary:* `ring_nf` is the *normal-form* variant of `ring`. While
`ring` *closes* a goal that is an identity in a (semi)commutative
ring, `ring_nf` instead *rewrites* both sides of the goal into a
canonical polynomial form. It is useful when `ring` does not close
the goal because it is not yet an equation (e.g. there are side
hypotheses) or when you want to simplify a hypothesis.

*Examples:*

:::table (align := left) +header
* + Proof state
  + Tactic
  + New proof state
* + `a b : ℝ` {br}`h : a * (b + b) = 6` {br}[] ⊢ ...
  + `ring_nf at h`
  + `a b : ℝ` {br}`h : 2 * (a * b) = 6` {br}[] ⊢ ...
:::

*Remarks:*

* `ring_nf` never fails; it just rewrites.
* Use `ring` to close a pure ring identity; use `ring_nf` to
  normalize one side before continuing with another tactic.
* You can target a hypothesis with `ring_nf at h` or normalize
  everywhere with `ring_nf at *`.



::::keepEnv
:::example " "
```lean
example (a b : ℝ) (h : a * (b + b) = 6) : 2 * (a * b) = 6 := by
  ring_nf at h ⊢
  linarith

example (x : ℝ) : (x + 1) * (x - 1) + 1 = x ^ 2 := by
  ring_nf
```

:::
::::
