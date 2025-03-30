import Lean
import VersoManual
import DemoTextbook
import UsersGuide.Markup
import Leancourse.Meta.Table
import Leancourse.Misc.Defs

open Verso.Genre Manual
open DemoTextbook.Exts

set_option pp.rawOnError true

#doc (Manual) "`use`" =>

**Proof state** **Command** **New proof state**
--------------------------- ----------------- -----------------------
`f : α → Prop` `use y,` `f : α → Prop`
`y : α` `y : α`
⊢ ∃ (x : α), f x` ⊢ f y`

**Summary:** The `use` tactic is used for goals that begin with ∃. Here, parameters are used to indicate which object quantified by ∃ is to be reused in the proof.

**Examples**

+----------------------------------+--------------+-----------------------+
| **Proof state** | **Command** | **New proof state** |
+:=================================+:=============+:======================+
| `⊢ ∃ (k : ℕ), k * k = 16` | | |
| | |
| & | | |
| | |
| `use 4, ` | | |
| | | |
| & | | |
| | | |
| `⊢ 4 * 4 = 16` | | |
+----------------------------------+--------------+-----------------------+
