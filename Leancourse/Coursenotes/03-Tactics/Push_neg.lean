import VersoManual
import Manual.Meta
import Leancourse.Misc.Defs

open Verso.Genre Manual

set_option pp.rawOnError true

#doc (Manual) "`push_neg`" =>

**Summary:** In many steps of a proof, a negation must be carried out. In order to process the corresponding quantifiers etc. as well and to better reusable, the tactic `push_neg` is available.

**Examples**
+---------------------+--------------+-----------------------+
| **Proof state** | **Command** | **New proof state** |
+:====================+:=============+:======================+
| `⊢ ¬(P ∨ Q)` | | |
| | | |
| & | | |
| | | |
| `push_neg,` | | |
| | | |
| & | | |
| | | |
| `⊢ ¬P ∧ ¬Q` | | |
+---------------------+--------------+-----------------------+

**Notes:**

This tactic also works with other objects, such as sets.
