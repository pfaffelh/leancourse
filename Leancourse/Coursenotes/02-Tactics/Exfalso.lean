import VersoManual
import Manual.Meta
import Leancourse.Misc.Defs

open Verso.Genre Manual
open MyDef

set_option pp.rawOnError true

#doc (Manual) "`exfalso`" =>
%%%
tag := "exfalso"
%%%

**Summary:** The statement `false → P` is true for all `P`. If the current goal is `⊢ P`, and you would apply this true statement using `apply`, the new goal would be `⊢ false`. This is exactly what the `exfalso` tactic does.

**Examples:**

:::table (align := left) (header := true)
* + Proof state
  + Tactic
  + New proof state
* + `h : P` {br}[] ⊢ Q
  + `exfalso`
  + `h : P` {br}[] ⊢ False
* + hP : P {br}[] hnP : ¬P {br}[] ⊢ Q
  + exfalso
  + hP : P {br}[] hnP: ¬P {br}[] ⊢ false
:::

**Remarks:**

* If you use this tactic, you leave the realm of constructive mathematics. (This dispenses with the rule of the excluded middle.)
* `exfalso` is the same as `apply False.elim`; see the examples for {ref "exact"}[`exact`].

::::keepEnv
:::example " "
```lean
example (P : Prop) : False → P := by
  exact False.elim
```
:::
::::
