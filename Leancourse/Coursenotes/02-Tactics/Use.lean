import VersoManual
import Manual.Meta
import Leancourse.Misc.Defs

open Verso.Genre Manual
open MyDef

set_option pp.rawOnError true

#doc (Manual) "`use`" =>
%%%
tag := "use"
%%%

:::table (align := left) (header := true)
* + Proof state
  + Tactic
  + New proof state
* + `f : α → Prop` {br}[] y : α {br}[] ∃ (x : α), f x
  + `use y`
  + `f : α → Prop` {br}[] y : α {br}[] f y
:::


**Summary:** The `use` tactic is used for goals that begin with `∃`. Here, parameters are used to indicate which object quantified by `∃` is to be reused in the proof.

**Examples**

:::table (align := left) (header := true)
* + Proof state
  + Tactic
  + New proof state
* + `⊢ ∃ (k : ℕ), k * k = 16`
  + use 4
  + `⊢ 4 * 4 = 16`
* + `⊢ ∃ (k l : ℕ), k * l = 16`
  + `use 8, 2`
  + `⊢ 8 * 2 = 16`
:::

::::keepEnv
:::example " "
```lean
example : ∃ (k : ℕ), k * k = 16 := by
  use 4
  rfl
```
```lean
example : ∃ (k : ℕ), k * k = 16 := by
  refine ⟨4, by rfl⟩
```

```lean
example (ε : ℝ) (hε : 0 < ε) : ∃ (δ : ℝ) (hδ : 0 < δ), δ < ε := by
  use ε / 2

  use 4
```
:::
::::
