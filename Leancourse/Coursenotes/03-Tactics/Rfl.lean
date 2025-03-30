import Lean
import VersoManual
import DemoTextbook
import UsersGuide.Markup
import Leancourse.Meta.Table
import Leancourse.Misc.Defs

open Verso.Genre Manual
open DemoTextbook.Exts

set_option pp.rawOnError true

#doc (Manual) "`rfl`" =>

**Summary:** This tactic proves the equality (or equivalence) of two definitionally equal terms.

**Examples:**

+-------------------------+----------------+-------------------------+
| **Proof state** | **Command** | **New proof state** |
+:========================+:===============+:========================+
| `⊢ P ↔ P` or | `refl,` | **goals accomplished** |
+-------------------------+----------------+-------------------------+
| `⊢ P = P` | | |
+-------------------------+----------------+-------------------------+
| `⊢ 1 + 2 = 3` | | |
| | | |
| & | | |
| | | |
| `refl,` | | |
| | | |
| & | | |
| | | |
| **goals accomplished** | | |
+-------------------------+----------------+-------------------------+

**Notes:**

The second example works because both sides are by definition equal to `succ succ succ 0`.
