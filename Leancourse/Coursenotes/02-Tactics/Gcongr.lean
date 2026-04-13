import Lean
import VersoManual
import Manual.Meta
import Leancourse.Misc.Defs
import Mathlib
open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open MyDef

set_option pp.rawOnError true

#doc (Manual) "`gcongr`" =>
%%%
tag := "gcongr"
%%%

*Summary:* `gcongr` ("generalized congruence") reduces a
monotonicity goal by peeling off a common outer context.  It turns
a goal like `f a + b ≤ f a' + b` into `a ≤ a'` whenever `f` is
known to be monotone in its argument.  It is the standard tool for
proving routine inequalities of compound expressions.

*Examples:*

:::table (align := left) +header
* + Proof state
  + Tactic
  + New proof state
* + `a a' b : ℝ` {br}`h : a ≤ a'` {br}[] ⊢ a + b ≤ a' + b
  + `gcongr`
  + `a a' b : ℝ` {br}`h : a ≤ a'` {br}[] ⊢ a ≤ a'
:::

*Remarks:*

* `gcongr` relies on lemmas tagged `@[gcongr]` in Mathlib. Common
  operations (`+`, `*`, `^`, `div`, `sum`, ...) are already tagged,
  so the tactic works out of the box in most situations.
* After `gcongr`, the remaining goals are usually closed by
  `assumption`, `linarith`, or `positivity`.
* `gcongr` can also prove strict inequalities.



::::keepEnv
:::example " "
```lean
example (a a' b : ℝ) (h : a ≤ a') : a + b ≤ a' + b := by
  gcongr

example (x y : ℝ) (hx : 0 ≤ x) (h : x ≤ y) : x ^ 2 ≤ y ^ 2 := by
  gcongr
```

:::
::::
