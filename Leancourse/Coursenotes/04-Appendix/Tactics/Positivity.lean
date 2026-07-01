import Lean
import VersoManual
import Manual.Meta
import Leancourse.Misc.Defs
import Mathlib
open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open MyDef

set_option pp.rawOnError true

#doc (Manual) "`positivity`" =>
%%%
tag := "positivity"
%%%

*Summary:* `positivity` proves goals of the form `0 < e`, `0 ≤ e`,
or `e ≠ 0`, where `e` is an arithmetic expression built from
literals and variables by operations that preserve positivity
(addition of nonnegatives, multiplication, powers, `abs`, `exp`,
square roots, ...).

*Examples:*

:::table (align := left) +header
* + Proof state
  + Tactic
  + New proof state
* + `x : ℝ` {br}`hx : 0 < x` {br}[] ⊢ 0 < x ^ 2 + 1
  + `positivity`
  + (no goals)
:::

*Remarks:*

* `positivity` is extensible: any `@[positivity]`-tagged lemma in
  Mathlib becomes available.
* When a term depends on a variable whose sign is unknown but you
  have a hypothesis `0 < y`, `positivity` will pick it up
  automatically.



::::keepEnv
:::example " "
```lean
example (x : ℝ) (hx : 0 < x) : 0 < x ^ 2 + 1 := by positivity
example (a b : ℝ) (ha : 0 < a) (hb : 0 < b) : 0 < a + b := by positivity
example (n : ℕ) : (0 : ℝ) ≤ n := by positivity
```

:::
::::
