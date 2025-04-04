import VersoManual
import Manual.Meta
import Leancourse.Misc.Defs
import Mathlib

open Verso.Genre Manual
open MyDef

set_option pp.rawOnError true

#doc (Manual) "`specialize`" =>
%%%
tag := "specialize"
%%%

:::table (align := left) (header := true)
* + Proof state
  + Tactic
  + New proof state
* + `f : ℕ → Prop` {br}[] `h : ∀ (n : ℕ), f n` {br}[] `⊢ P`
  + `specialize h 13`
  + `f: ℕ → Prop` {br}[] `h : f 13` {br}[] `⊢ P`
:::

**Summary:** In a hypothesis `h : ∀ n, ...`, `...` applies to all `n`, but for the proof of the goal, you may only need a specific `n`. If you specify `specialize h` followed by the value for which `h` is needed, the hypothesis changes accordingly.

**Examples**

```lean
example (p : ℕ → Prop) (hp : ∀ (n : ℕ), p n) :
    (p 0) := by
  specialize hp 0
  exact hp
```

**Remarks**

* Just as with `use`, you have to be careful that the goal remains provable.
* If you want to use two values of the hypothesis `h`, then `let h' := h` first provides a duplication of the hypothesis, so that you can then apply `specialize` to `h` and `h'`.

::::keepEnv
:::example " "
```lean
example (P : Prop) : False → P := by
  exact False.elim
```
:::
::::
