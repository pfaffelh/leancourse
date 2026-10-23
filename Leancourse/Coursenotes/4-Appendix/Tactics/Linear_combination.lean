import Lean
import VersoManual
import Manual.Meta
import Leancourse.Misc.Defs
import Mathlib
open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open MyDef

set_option pp.rawOnError true

#doc (Manual) "`linear_combination`" =>
%%%
tag := "linear-combination"
%%%

*Summary:* `linear_combination` proves an *equality* goal from
equality hypotheses.  You supply an explicit linear (or polynomial)
combination of the hypotheses that equals the goal; the tactic
subtracts it from the goal and discharges the remainder with `ring`.
It is the tactic to reach for when `linarith` cannot help because the
goal is an equality that follows by algebraic manipulation.

*Examples:*

::::keepEnv
:::example " "
```lean
example (x y : ℝ) (h1 : x + y = 3) (h2 : x - y = 1) :
    x = 2 := by
  linear_combination (h1 + h2) / 2
```
:::
::::

*Remarks:*

* You provide the coefficients; the tactic verifies them.  Here
  `(h1 + h2) / 2` says "add the two equations and halve", which gives
  exactly `x = 2`.
* The leftover after subtracting your combination must be closed by
  `ring`, so any *polynomial* identity in the coefficients is allowed,
  not just linear ones.
* If you do not know the combination, {ref "polyrith"}[`polyrith`] can
  often find it for you and print a `linear_combination` call.
