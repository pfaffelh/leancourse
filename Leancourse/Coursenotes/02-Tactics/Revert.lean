import VersoManual
import Manual.Meta
import Leancourse.Misc.Defs

open Verso.Genre Manual
open MyDef

set_option pp.rawOnError true

#doc (Manual) "`revert`" =>
%%%
tag := "revert"
%%%

**Summary:** `revert` is the opposite of `intro`: It takes a hypothesis from the local context and inserts it as a precondition into the goal.

**Examples**

:::table (align := left) (header := true)
* + Proof state
  + Tactic
  + New proof state
* + `h : P` {br}[] ⊢ Q
  + `revert hP`
  + `⊢ P → Q`
:::

::::keepEnv
:::example " "
```lean
example (P : Prop) : False → P := by
  exact False.elim
```
:::
::::

**Remarks:**

`revert` is rarely needed; actually only when you want to apply an already proven result exactly and first want to establish the correct form of the goal.
