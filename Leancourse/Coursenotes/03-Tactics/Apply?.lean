import Lean
import VersoManual
import DemoTextbook
import UsersGuide.Markup
import Manual.Meta.Table
import Leancourse.Misc.Defs

open Verso.Genre Manual
open DemoTextbook.Exts

set_option pp.rawOnError true

#doc (Manual) "`apply?`" =>

**Summary:** There are already a lot of proven statements in `mathlib`. When using `apply?`, the `mathlib` is statements whose types correspond to those of the statement to be proved. If this is not successful, `Lean` reports a `timeout`. If successful, it also reports which command was found. If you click on it, this is inserted in place of `library_search`.

**Examples**

**Proof state** **Command** **New proof state**
--------------------- -------------------------- -------------------------------
`h1 : a < b` `library_search,` **goals accomplished**
`h2 : b < c` `Try this: `
`⊢ a < c` `exact lt_trans h1 h2`

**Notes**

The tactic `suggest` is similar and also works if
the goal cannot be closed.
