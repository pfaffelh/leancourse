import VersoManual
import Manual.Meta
import Leancourse.Misc.Defs

open Verso.Genre Manual

set_option pp.rawOnError true

#doc (Manual) "`change`" =>

Changes the goal (or a hypothesis) into a goal (or a hypothesis) that is defined the same.

**Examples:**

**Notes:**

* As can be seen from the penultimate example, `change` also works for hypotheses.
* Since many tactics test for definitional equality anyway, `change` is often not necessary. However, it can help to make the proof more readable.
