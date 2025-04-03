import VersoManual
import Manual.Meta
import Leancourse.Misc.Defs

open Verso.Genre Manual
open MyDef

set_option pp.rawOnError true

#doc (Manual) "`clear`" =>
%%%
tag := "clear"
%%%

:::table (align := left) (header := true)
* + Proof state
  + Tactic
  + New proof state
* + `h : P` {br}[] `⊢ Q`
  + `clear h`
  + `⊢ Q`
:::

**Summary:** With `clear h` the hypothesis `h` is removed from the goal state
(forgotten).

**Examples:**

**Proof state** **Command** **New proof state**
----------------- ------------------- -----------------------
