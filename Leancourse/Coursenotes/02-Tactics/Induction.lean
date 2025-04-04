import VersoManual
import Manual.Meta
import Leancourse.Misc.Defs
import Mathlib

open Verso.Genre Manual
open MyDef

set_option pp.rawOnError true

#doc (Manual) "`induction`" =>
%%%
tag := "induction"
%%%

**Summary:**

Inductive types allow the possibility of proving statements about them by means of induction. This includes, for example, the usual case of complete induction over natural numbers.

**Examples**

:::table (align := left) (header := true)
* + Proof state
  + Tactic
  + New proof state
* + `n : ℕ` {br}[] ⊢ n = 0 + n
  + induction n with {br}[] `| zero ↦ ?_` {br}[] | `succ n hn ↦ ?_`
  + ⊢ 0 = 0 + 0 {br}[] hd : d = 0 + d {br}[] ⊢ d.succ = 0 + d.succ
:::

::::keepEnv
:::example " "
```lean
example (n : ℕ) : n = 0 + n := by
  induction n with
  | zero =>
    rfl
  | succ n hn =>
    rw [← add_assoc, ← hn]
```
:::
::::
