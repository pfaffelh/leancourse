import VersoManual
import Manual.Meta
import Leancourse.Misc.Defs

open Verso.Genre Manual
open MyDef

set_option pp.rawOnError true

#doc (Manual) "`right`" =>
%%%
tag := "right"
%%%

**Summary:** See `left`, where the adjustments are obvious.

**Examples**

:::table (align := left) (header := true)
* + Proof state
  + Tactic
  + New proof state
* + `h : P ∨ Q`
  + `right`
  + `⊢ Q`
:::
