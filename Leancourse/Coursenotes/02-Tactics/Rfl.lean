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
* + `⊢ P ↔ P` oder {br}[] `⊢ P = P`
  + `rfl`
  + **no goals**
* + `⊢ 1 + 2 = 3`
  + `rfl`
  + **no goals**
:::

**Notes:**

The second example works because both sides are by definition equal to `succ succ succ 0`.
