import VersoManual
import Manual.Meta
import Leancourse.Misc.Defs

open Verso.Genre Manual
open MyDef

set_option pp.rawOnError true

#doc (Manual) "`triv`" =>
%%%
tag := "triv"
%%%

**Summary**

`triv` solves an objective that is, by definition, identical to `true`. It also solves objectives that can be solved with `refl`
.

**Examples**

:::table (align := left) (header := true)
* + Proof state
  + Tactic
  + New proof state
* + `⊢ True`
  + `triv`
  + **No goals**
* + `⊢ x = x`
  + `triv`
  + **No goals**
:::

::::keepEnv
:::example " "
```lean
example (P : Prop) : False → P := by
  exact False.elim
```
:::
::::
