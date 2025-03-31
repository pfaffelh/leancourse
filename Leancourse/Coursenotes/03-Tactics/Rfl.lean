import VersoManual
import Manual.Meta
import Leancourse.Misc.Defs

open Verso.Genre Manual

set_option pp.rawOnError true

#doc (Manual) "`rfl`" =>
%%%
tag := "rfl"
%%%

**Summary:** This tactic proves the equality (or equivalence) of two definitionally equal terms.

**Examples:**

:::table (align := left) (header := true)
* + Proof state
  + Tactic
  + New proof state
* + `h : P` {br}[] ⊢ P
  + `exact h`
  + **no goals**

+-------------------------+----------------+-------------------------+
| **Proof state** | **Command** | **New proof state** |
+:========================+:===============+:========================+
| `⊢ P ↔ P` or | `refl,` | **goals accomplished** |
+-------------------------+----------------+-------------------------+
| `⊢ P = P` | | |
+-------------------------+----------------+-------------------------+
| `⊢ 1 + 2 = 3` | | |
| | | |
| & | | |
| | | |
| `refl,` | | |
| | | |
| & | | |
| | | |
| **goals accomplished** | | |
+-------------------------+----------------+-------------------------+

**Notes:**

The second example works because both sides are by definition equal to `succ succ succ 0`.
