import VersoManual
import Manual.Meta
import Leancourse.Misc.Defs

open Verso.Genre Manual
open MyDef

set_option pp.rawOnError true

#doc (Manual) "`tauto`" =>
%%%
tag := "tauto"
%%%

**Summary:** `tauto` solves all goals that can be solved with a truth table.

**Examples**

:::table (align := left) (header := true)
* + Proof state
  + Tactic
  + New proof state
* + ⊢ P ∧ Q → P
  + `tauto` oder `tauto!`
  + **no goals**
* + ⊢ ((P → Q) → P) → P
  + `tauto!`
  + **no goals**
:::

The truth tables for `¬P`, `P ∧ Q` and `P ∨ Q` are as follows; if more terms of type `Prop` are involved, there are more lines.

:::table
* + `P`
  + `¬P`
* + `true`
  + `false`
* + `false`
  + `true`
:::

:::table
* + `P`
  + `Q`
  + `(P ∧ Q)`
* + `true`
  + `true`
  + `true`
* + `false`
  + `true`
  + `false`
* + `true`
  + `false`
  + `false`
* + `false`
  + `false`
  + `false`
:::

:::table
* + `P`
  + `Q`
  + `(P ∨ Q)`
* + `true`
  + `true`
  + `true`
* + `false`
  + `true`
  + `true`
* + `true`
  + `false`
  + `true`
* + `false`
  + `false`
  + `false`
:::

**Notes**

The difference between `tauto` and `tauto!` is that in the latter tactic, the rule of the excluded middle is allowed.  The second example can therefore only be solved with `tauto!`, but not with `tauto`.
