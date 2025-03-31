import VersoManual
import Manual.Meta
import Leancourse.Misc.Defs

open Verso.Genre Manual

set_option pp.rawOnError true

#doc (Manual) "`use`" =>
%%%
tag := "use"
%%%

**Proof state** **Command** **New proof state**
--------------------------- ----------------- -----------------------
`f : α → Prop` `use y,` `f : α → Prop`
`y : α` `y : α`
⊢ ∃ (x : α), f x` ⊢ f y`

**Summary:** The `use` tactic is used for goals that begin with ∃. Here, parameters are used to indicate which object quantified by ∃ is to be reused in the proof.

**Examples**

:::table (align := left) (header := true)
* + Proof state
  + Tactic
  + New proof state
* + `h : P` {br}[] ⊢ P
  + `exact h`
  + **no goals**

+----------------------------------+--------------+-----------------------+
| **Proof state** | **Command** | **New proof state** |
+:=================================+:=============+:======================+
| `⊢ ∃ (k : ℕ), k * k = 16` | | |
| | |
| & | | |
| | |
| `use 4, ` | | |
| | | |
| & | | |
| | | |
| `⊢ 4 * 4 = 16` | | |
+----------------------------------+--------------+-----------------------+

mal sehen
