import Lean
import VersoManual
import DemoTextbook
import UsersGuide.Markup
import Leancourse.Meta.Table
import Leancourse.Misc.Defs

open Verso.Genre Manual
open DemoTextbook.Exts

set_option pp.rawOnError true

#doc (Manual) "`linarith`" =>

**Summary:** This tactic can prove equations and inequalities with the help of hypotheses. It is important that the hypotheses used are also only equations and inequalities. So here we are working mainly with the transitivity of `<` together with arithmetic rules.

**Examples:**

**Proof state** **Command** **New proof state**
---------------------- -------------------- -------------------------
`h1 : a < b` `linarith,` **goals accomplished**
`h2 : b ≤ c`
`⊢ a < c`
