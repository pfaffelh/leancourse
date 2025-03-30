import Lean
import VersoManual
import DemoTextbook
import UsersGuide.Markup
import Leancourse.Meta.Table
import Leancourse.Misc.Defs

open Verso.Genre Manual
open DemoTextbook.Exts

set_option pp.rawOnError true

#doc (Manual) "`constructor`" =>

**Summary:** If the goal is of the type `⊢ P ∧ Q`, it is replaced by `constructor` into two goals `⊢ P` and `⊢ Q`.

**Examples**

**Proof state** **Command** **New proof state**
------------------ ----------------- -----------------------
`⊢ P ∧ Q` `split,` `⊢ P`
`⊢ Q`
`⊢ P ↔ Q` `split,` `⊢ P → Q`
`⊢ Q → P`

**Notes**

Note that `⊢ P ↔ Q` is identical to `⊢ (P → Q) ∧ (Q → P)`.
