import Lean
import VersoManual
import DemoTextbook
import UsersGuide.Markup
import Leancourse.Meta.Table
import Leancourse.Misc.Defs

open Verso.Genre Manual
open DemoTextbook.Exts

set_option pp.rawOnError true

#doc (Manual) "`congr`" =>

**Summary:** If you have to show an equality `f x = f y`, then `congr` uses the statement that the equality is particularly true if `x = y`.

**Examples:**


**Notes:**

The related tactic `congr'` uses another parameter that determines how many recursive layers are eliminated in the goal. This is helpful in the following examples:
