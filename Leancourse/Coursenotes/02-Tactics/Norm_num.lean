import VersoManual
import Manual.Meta
import Leancourse.Misc.Defs

open Verso.Genre Manual
open MyDef

set_option pp.rawOnError true

#doc (Manual) "`norm_num`" =>
%%%
tag := "norm_num"
%%%

**Summary:**

As long as there are no variables, `norm_num` can do calculations which involve `=`, `<`, `≤` or `≠`.

**Examples:**

:::table (align := left) (header := true)
* + Proof state
  + Tactic
  + New proof state
* + `⊢ 2 + 2 < 5`
  + `norm_num`
  + **no goals**
* + `⊢ | (1 : ℝ) | = 1`
  + `norm_num`
  + **no goals**
:::

**Notes**

`norm_num` knows about some more operations, e.g. absolute values; see also the second example.
