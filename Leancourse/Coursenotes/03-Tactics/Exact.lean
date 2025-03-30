import VersoManual
import Manual.Meta
import Leancourse.Misc.Defs

open Verso.Genre Manual

set_option pp.rawOnError true

#doc (Manual) "`exact`" =>
%%%
tag := "exact"
%%%

**Summary:** If the goal can be achieved with a single command, then it can be achieved with the `exact` tactic. Like many other tactics, `exact` also works with terms that are defined the same.

**Examples:**

+----------------------------+-------------------+-------------------------+
| **Proof state** | **Command** | **New proof state** |
+:===========================+:==================+:========================+
| `h : P` | `exact h,` | **goals accomplished** |
+----------------------------+-------------------+-------------------------+
| `⊢ P` | | |
+----------------------------+-------------------+-------------------------+
| `hP: P`\ | | |
| `hQ: Q`\ | | |
| `⊢ P ∧ Q` | | |
| | | |
| & | | |
| | | |
| `exact ⟨ hP, hQ ⟩,` | | |
| | | |
| & | | |
| | | |
| **goals accomplished** | | |
+----------------------------+-------------------+-------------------------+

**Notes:**

In the third example, note the order in which the two hapotheses `hP` and `hnP` are applied. The first hypothesis after `exact` is always the one whose right side matches the goal. If the goal requires further input, it is appended afterwards.
