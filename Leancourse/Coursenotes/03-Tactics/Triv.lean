import VersoManual
import Manual.Meta
import Leancourse.Misc.Defs

open Verso.Genre Manual

set_option pp.rawOnError true

#doc (Manual) "`triv`" =>
%%%
tag := "triv"
%%%

**Summary**

`triv` solves an objective that is, by definition, identical to `true`. It also solves objectives that can be solved with `refl`
.

**Examples**

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
| `⊢ true` | `triv,` | **goals accomplished** |
+-------------------------+----------------+-------------------------+
| `⊢ x=x` | | |
| | | |
| & | | |
| | | |
| `triv,` | | |
| | | |
| & | | |
| | | |
| **goals accomplished** | | |
+-------------------------+----------------+-------------------------+
