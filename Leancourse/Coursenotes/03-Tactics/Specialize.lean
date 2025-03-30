import VersoManual
import Manual.Meta
import Leancourse.Misc.Defs

open Verso.Genre Manual

set_option pp.rawOnError true

#doc (Manual) "`specialize`" =>
%%%
tag := "specialize"
%%%

**Proof state** **Command** **New proof state**
----------------------------- --------------------------- -----------------------
`f : ℕ → Prop` `specialize h 13,` `f: ℕ → Prop`
`h : ∀ (n : ℕ), f n` `h : f 13`
`⊢ P` `⊢ P`

**Summary:** In a hypothesis `h : ∀ n, ...`, `...` applies to all `n`, but for the proof of the goal, you may only need a specific `n`. If you specify `specialize h` followed by the value for which `h` is needed, the hypothesis changes accordingly.

**Examples**

+-----------------------------------+--------------+-----------------------+
| **Proof state** | **Command** | **New proof state** |
+:==================================+:=============+:======================+
| `h: ∀ (n : ℕ), 0 < n + 1`\ | | |
| `⊢ 0 < 1` | | |
| | | |
| & | | |
| | | |
| `specialize h 0,` | | |
| | | |
| & | | |
| | | |
| `m : ℕ`\ | | |
| `h: 0 < 0 + 1`\ | | |
| `⊢ 0 < 1` | | |
+-----------------------------------+--------------+-----------------------+

**Notes**

* Just as with `use`, you have to be careful that the goal remains provable.
* If you want to use two values of the hypothesis `h`, then `let h' := h` first provides a duplication of the hypothesis, so that you can then apply `specialize` to `h` and `h'`.
