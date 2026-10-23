import Lean
import VersoManual
import Manual.Meta
import Leancourse.Misc.Defs
import Mathlib
open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open MyDef

set_option pp.rawOnError true

#doc (Manual) "`fun_prop`" =>
%%%
tag := "fun-prop"
%%%

*Summary:* `fun_prop` is a general-purpose tactic for closing
function-property goals such as `Continuous f`, `Measurable f`,
`Differentiable ℝ f`, `ContDiff ℝ n f`, `Integrable f`, and others.
It works by recursively applying composition, linearity, and other
structural lemmas tagged `@[fun_prop]` in Mathlib.

*Examples:*

:::table (align := left) +header
* + Proof state
  + Tactic
  + New proof state
* + `⊢ Continuous (fun x : ℝ => x^2 + Real.sin x)`
  + `fun_prop`
  + `no goals 🎉`
:::

*Remarks:*

* `fun_prop` subsumes and replaces the older `continuity` and
  `measurability` tactics for most purposes.
* For arguments it does not know about (e.g. the continuity of a
  user-defined function), supply the fact as a hypothesis or add
  a `@[fun_prop]` lemma.
* When `fun_prop` fails, it will often report a helpful subgoal
  indicating which atomic fact is missing.



::::keepEnv
:::example " "
```lean
example : Continuous (fun x : ℝ => x ^ 2 + Real.sin x) := by
  fun_prop

example : Measurable (fun x : ℝ => x ^ 3 + 2 * x) := by
  fun_prop
```

:::
::::
