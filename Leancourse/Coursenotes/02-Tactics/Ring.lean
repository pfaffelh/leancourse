import VersoManual
import Manual.Meta
import Leancourse.Misc.Defs

open Verso.Genre Manual
open MyDef

set_option pp.rawOnError true

#doc (Manual) "`ring`" =>
%%%
tag := "ring"
%%%

**Summary:** The `ring` uses rules of calculation such as associativity, commutativity, and distributivity to achieve the goal.

**Examples**

:::table (align := left) (header := true)
* + Proof state
  + Tactic
  + New proof state
* + `x y : ℝ` {br}[] ⊢ x + y = y + x
  + `ring`
  + **no goals**
* + `n : ℕ` {br}[] `⊢ (n + 1)^2 = n^2 + 2*n + 1`
  + `ring`
  + **no goals**
:::

**Notes:**

* The second example works even though `ℕ` is not a ring (but only a half-ring). It would also work with `n : ℝ` (since `ℝ` has more calculation rules than `ℕ`).
* `ring` is only used to close the goal.
