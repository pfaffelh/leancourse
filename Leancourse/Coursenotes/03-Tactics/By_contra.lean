import Lean
import VersoManual
import DemoTextbook
import UsersGuide.Markup
import Leancourse.Meta.Table
import Leancourse.Misc.Defs

open Verso.Genre Manual
open DemoTextbook.Exts

set_option pp.rawOnError true

#doc (Manual) "`by_contra`" =>

**Summary**

The `by_contra` tactic provides a proof by contradiction. It is therefore assumed (i.e. transformed into a hypothesis) that the statement (after `⊢`) is not true, and this must be made to contradict itself, i.e. a proof of `false` must be found.

**Examples**

+---------------------------+-----------------------+-----------------------+
| **Proof state** | **Command** | **New proof state** |
+:==========================+:======================+:======================+
| `⊢ P` | `by_contra h,` | `h : ¬P` |
+---------------------------+-----------------------+-----------------------+
| | | `⊢ false` |
+---------------------------+-----------------------+-----------------------+
| `h: ¬¬P`\ | | |
| `⊢ P` | | |
| | | |
| & | | |
| | | |
| `by_contra hnegP,` | | |
| | | |
| & | | |
| | | |
| `h: ¬¬P`\ | | |
| `hnegP: ¬P`\ | | |
| `⊢ false` | | |
+---------------------------+-----------------------+-----------------------+

**Notes**

This tactic is stronger than `exfalso`. After all, there the goal is only converted to `false` without adding a new hypothesis. With `by_contra`, the new goal is also `false`, but there is still a new hypothesis.
