import VersoManual
import Manual.Meta
import Manual.Meta.Table
import Leancourse.Misc.Defs
import Mathlib

open Verso.Genre Manual
open Lean.MessageSeverity
open MyDef

set_option pp.rawOnError true

#doc (Manual) "`apply?`" =>
%%%
tag := "apply?"
%%%

**Summary:** There are already a lot of proven statements in `Mathlib`. When using `apply?`, `Mathlib` is searched for statements whose types correspond to those of the statement to be proved. If this is not successful, `Lean` reports a `timeout`. If successful, it also reports which commands were found. If you click on it, this is inserted in place of `apply?`.

**Examples**

:::table (align := left) (header := true)
* + Proof state
  + Tactic
  + New proof state
* + `h₁ : a < b` {br}[] `h₂ : b < c`
  + `apply?`
  + **no goals** {br}[] Try this: `exact lt_trans h₁ h₂`
:::

::::keepEnv
:::example " "
```lean (name := output)
example (n : ℕ) : 2 * n = n + n := by
  apply?
```

```leanOutput output (severity := information)
Try this: exact Nat.two_mul n
```

{docstring Lean.Parser.Tactic.apply?}

:::
::::
