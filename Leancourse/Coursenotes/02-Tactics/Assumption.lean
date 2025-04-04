import VersoManual
import Manual.Meta
import Leancourse.Misc.Defs

open Verso.Genre Manual
open MyDef

set_option pp.rawOnError true

#doc (Manual) "`assumption`" =>
%%%
tag := "assumption"
%%%

**Summary:**
If a hypothesis is identical to the goal, `assumption` closes the goal.

**Examples**

:::table (align := left) (header := true)
* + Proof state
  + Tactic
  + New proof state
* + `h : P` {br}[] `⊢ P`
  + `assumption`
  + **no goals**
* + `h : ¬P` {br}[] `⊢ P → False`
  + `assumption`
  + **no goals**
:::

::::keepEnv
:::example " "
```lean
example (hP : P) (hQ : Q) : P ∧ Q := by
  constructor <;> assumption
```

```lean
example (P : Prop) (hP : P) : P := by
  assumption
```
:::
::::

**Notes**

* As in other tactics, `assumption` works up to definitional equality.
* Here is a trick: If you use `<;>` after a tactic, the forthcoming tactic is applied to apll goals.
