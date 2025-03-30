import Lean
import VersoManual
import DemoTextbook
import UsersGuide.Markup
import Leancourse.Meta.Table
import Leancourse.Misc.Defs

open Verso.Genre Manual
open DemoTextbook.Exts

set_option pp.rawOnError true

#doc (Manual) "`clear`" =>


**Summary:** With `clear h` the hypothesis `h` is removed from the goal state
(forgotten).

**Examples:**

**Proof state** **Command** **New proof state**
----------------- ------------------- -----------------------
`h : P` `clear h,` `⊢ Q`
`⊢ Q`
