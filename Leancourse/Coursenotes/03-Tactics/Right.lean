import VersoManual
import Manual.Meta
import Leancourse.Misc.Defs

open Verso.Genre Manual

set_option pp.rawOnError true

#doc (Manual) "`right`" =>

**Summary:** See `left`, where the adjustments are obvious.

**Examples**

**Proof state** **command** **New proof state**
------------------ ----------------- -----------------------
`⊢ P ∨ Q` `right,` `⊢ Q`
