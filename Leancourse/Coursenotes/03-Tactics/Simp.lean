import Lean
import VersoManual
import DemoTextbook
import UsersGuide.Markup
import Leancourse.Meta.Table
import Leancourse.Misc.Defs

open Verso.Genre Manual
open DemoTextbook.Exts

set_option pp.rawOnError true

#doc (Manual) "`simp`" =>

**Summary:** In `mathlib` there are many lemmas with `=` or `↔` statements that can be applied with `rw` and are marked with `@[simp]`. These marked lemmas have the property that the right side is a simplified form of the left side. With `simp`, `lean` looks for matching lemmas and tries to apply them.

**Examples**


**Notes:**

If you want to know which lemmas were used, try 'simp?` or 'squeeze_simp`. This provides clues.

+---------------------------------+--------------+-----------------------+
| **Proof state** | **Command** | **New proof state** |
+:================================+:=============+:======================+
| `⊢ n + 0 = n` | | |
| | | |
| & | | |
| | | |
| `simp?,` | | |
| | | |
| & | | |
| | | |
| **goals accomplished**\ | | |
| Try this:\ | | |
| `simp only [add_zero, `\ | | |
| ` eq_self_iff_true]` | | |
+---------------------------------+--------------+-----------------------+
