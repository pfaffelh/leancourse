import Lean
import VersoManual
import DemoTextbook
import UsersGuide.Markup
import Leancourse.Meta.Table
import Leancourse.Misc.Defs

open Verso.Genre Manual
open DemoTextbook.Exts

set_option pp.rawOnError true

#doc (Manual) "`right`" =>

**Summary:** See `left`, where the adjustments are obvious.

**Examples**

**Proof state** **command** **New proof state**
------------------ ----------------- -----------------------
`⊢ P ∨ Q` `right,` `⊢ Q`
