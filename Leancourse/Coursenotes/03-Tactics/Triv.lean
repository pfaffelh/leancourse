import Lean
import VersoManual
import DemoTextbook
import UsersGuide.Markup
import Leancourse.Meta.Table
import Leancourse.Misc.Defs

open Verso.Genre Manual
open DemoTextbook.Exts

set_option pp.rawOnError true

#doc (Manual) "`triv`" =>

**Summary**

`triv` solves an objective that is, by definition, identical to `true`. It also solves objectives that can be solved with `refl`
.

**Examples**

+-------------------------+----------------+-------------------------+
| **Proof state** | **Command** | **New proof state** |
+:========================+:===============+:========================+
| `⊢ true` | `triv,` | **goals accomplished** |
+-------------------------+----------------+-------------------------+
| `⊢ x=x` | | |
| | | |
| & | | |
| | | |
| `triv,` | | |
| | | |
| & | | |
| | | |
| **goals accomplished** | | |
+-------------------------+----------------+-------------------------+
