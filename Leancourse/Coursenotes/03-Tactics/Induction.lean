import VersoManual
import Manual.Meta
import Leancourse.Misc.Defs

open Verso.Genre Manual

set_option pp.rawOnError true

#doc (Manual) "`induction`" =>

**Summary:**

Inductive types allow the possibility of proving statements about them by means of induction. This includes, for example, the usual case of complete induction over natural numbers.

**Examples**

**Proof state** **command** **new proof state**
---------------------- --------------------------------- ---------------------------------
`n : ℕ` `induction n with d hd,` `⊢ 0 = 0 + 0`
`⊢ n = 0 + n` `hd : d = 0 + d`
`⊢ d.succ = 0 + d.succ,`
