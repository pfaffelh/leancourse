import Lean
import VersoManual
import DemoTextbook
import UsersGuide.Markup
import Manual.Meta.Table
import Leancourse.Misc.Defs
import Mathlib

open Verso.Genre Manual
open DemoTextbook.Exts
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

```lean
example (n : ℕ) : 2 * n = n + n := by
  apply?
```

```lean
example (n : ℕ) : n ^ 2 ≤ 2 ^ n := by
  apply? -- gives a list of results which are not useful
```

**Notes**

The tactic `suggest` is similar and also works if
the goal cannot be closed.
