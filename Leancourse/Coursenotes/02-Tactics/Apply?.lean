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
%%%
tag := "apply?"
%%%

**Summary:** There are already a lot of proven statements in `mathlib`. When using `apply?`, the `mathlib` is statements whose types correspond to those of the statement to be proved. If this is not successful, `Lean` reports a `timeout`. If successful, it also reports which command was found. If you click on it, this is inserted in place of `library_search`.

**Examples**

:::table (align := left) (header := true)
* + Proof state
  + Tactic
  + New proof state
* + `h₁ : a < b` {br}[] `h₂ : b < c`
  + `apply?`
  + **no goals** {br}[] Try this: `exact lt_trans h₁ h₂`
:::

**Notes**

The tactic `suggest` is similar and also works if
the goal cannot be closed.
