import VersoManual
import Manual.Meta
import Leancourse.Misc.Defs

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open MyDef

set_option pp.rawOnError true

#doc (Manual) "`clear`" =>
%%%
tag := "clear"
%%%

*Summary:* With `clear h` the hypothesis `h` is removed from the goal state
(forgotten).

*Example*

:::table (align := left) +header
* + Proof state
  + Tactic
  + New proof state
* + `h : P` {br}[] `⊢ Q`
  + `clear h`
  + `⊢ Q`
:::
