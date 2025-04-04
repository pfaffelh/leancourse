import VersoManual
import Manual.Meta
import Leancourse.Misc.Defs

open Verso.Genre Manual
open MyDef

set_option pp.rawOnError true

#doc (Manual) "`exact`" =>
%%%
tag := "exact"
%%%

**Summary:** If the goal can be closed with a single command, then it can be closed with the `exact` tactic. Like many other tactics, `exact` also works with terms that are definitionally equal.

**Examples:**

:::table (align := left) (header := true)
* + Proof state
  + Tactic
  + New proof state
* + `h : P` {br}[] ⊢ P
  + `exact h`
  + **no goals**
* + `hP: P` {br}[] `hQ: Q` `⊢ P ∧ Q`
  + `exact ⟨ hP, hQ ⟩`
  + **no goals**
:::

**Remarks:**

* The related tyctics `exact?` searches for terms which close the goal; see [`apply?`](apply?).
* If the proof consists of a single call of `exact`, it is easy to translate it to `term` mode; see [easy proofs in term mode](term).
* In the third example, note the order in which the two hypotheses `hP` and `hnP` are applied. The first hypothesis after `exact` is always the one whose right side matches the goal. If the goal requires further input, it is appended afterwards.

::::keepEnv
:::example " "
```lean
example (P : Prop) (h : False) : P := by
  exact False.elim h
```
:::
::::
