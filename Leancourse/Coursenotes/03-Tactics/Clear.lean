import VersoManual
import Manual.Meta
import Leancourse.Misc.Defs

open Verso.Genre Manual

set_option pp.rawOnError true

#doc (Manual) "`clear`" =>


**Summary:** With `clear h` the hypothesis `h` is removed from the goal state
(forgotten).

**Examples:**

**Proof state** **Command** **New proof state**
----------------- ------------------- -----------------------
`h : P` `clear h,` `⊢ Q`
`⊢ Q`
