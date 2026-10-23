import VersoManual
import Manual.Meta
import Leancourse.Markup

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open MyDef

set_option pp.rawOnError true

#doc (Manual) "`tauto`" =>
%%%
tag := "tauto"
%%%

*Summary:* `tauto` solves all goals that can be solved with a truth table.

*Examples*

:::table (align := left) +header
* + Proof state
  + Tactic
  + New proof state
* + ⊢ P ∧ Q → P
  + `tauto`
  + *No goals*
* + ⊢ ((P → Q) → P) → P
  + `tauto`
  + *No goals*
* + ⊢ ¬(P ∧ Q) ↔ ¬P ∨ ¬Q
  + `tauto`
  + *No goals*
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

*Notes*

Reasoning by truth table assumes that every proposition is either true or false. So `tauto` uses the law of the excluded middle, and the second example above — Peirce's law — is proved by it.

The constructive counterpart is {ref "itauto"}[`itauto`], which never uses that law. Comparing the two is how you find out whether a statement really needs classical logic.

