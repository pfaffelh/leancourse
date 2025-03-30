import Lean
import VersoManual
import DemoTextbook
import UsersGuide.Markup
import Leancourse.Meta.Table
import Leancourse.Misc.Defs

open Verso.Genre Manual
open DemoTextbook.Exts

set_option pp.rawOnError true

#doc (Manual) "`revert`" =>

**Summary:** `revert` is the opposite of `intro`: It takes a hypothesis from the local context and inserts it as a precondition into the goal.

**Examples**

+--------------------+--------------+-----------------------+
| **Proof state** | **Command** | **New proof state** |
+:===================+:=============+:======================+
| `hP : P`\ | | |
| `⊢ Q` | | |
| | | |
| & | | |
| | | |
| `revert hP` | | |
| | | |
| & | | |
| | | |
| `⊢ P → Q` | | |
+--------------------+--------------+-----------------------+

**Notes:**

`revert` is rarely needed; actually only when you want to apply an already proven result exactly and first want to establish the correct form of the goal.
