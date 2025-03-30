import Lean
import VersoManual
import DemoTextbook
import UsersGuide.Markup
import Leancourse.Meta.Table
import Leancourse.Misc.Defs

open Verso.Genre Manual
open DemoTextbook.Exts

set_option pp.rawOnError true

#doc (Manual) "`exfalso`" =>

**Summary:** The statement `false → P` is true for all `P`. If the current goal is `⊢ P`, and you would apply this true statement using `apply`, the new goal would be `⊢ false`. This is exactly what the `exfalso` tactic does.

**Examples:**

+--------------------+-------------------+-----------------------+
| **Proof state** | **Command** | **New proof state** |
+:===================+:==================+:======================+
| `h : P` | `exfalso,` | `h : P` |
+--------------------+-------------------+-----------------------+
| `⊢ Q` | | `⊢ false` |
+--------------------+-------------------+-----------------------+
| `hP: P`\ | | |
| `hnP: ¬P`\ | | |
| `⊢ Q` | | |
| | | |
| & | | |
| | | |
| `exfalso, ` | | |
| | | |
| & | | |
| | | |
| `hP: P`\ | | |
| `hnP: ¬P`\ | | |
| `⊢ false` | | |
+--------------------+-------------------+-----------------------+

**Notes:**

If you use this tactic, you leave the realm of constructive mathematics. (This dispenses with the rule of the excluded middle.)
