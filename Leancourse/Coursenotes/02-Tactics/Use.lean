import VersoManual
import Manual.Meta
import Leancourse.Misc.Defs
import Mathlib

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

In this example, `Lean` knows that `4 * 4 = 16` by `rfl`, so we need not type it.
```lean
example : ∃ (k : ℕ), k * k = 16 := by
  use 4
```

In various cases, `refine` can be used instead of `use`, e.g. here:
```lean
example : ∃ (k : ℕ), k * k = 16 := by
  refine ⟨4, by rfl⟩
```

Sometimes, one not only needs to give a term (e.g. `δ : ℝ`), but also a property (e.g. `hδ : 0 < δ`). This means we have to give two terms:
```lean
example (ε : ℝ) (hε : 0 < ε) : ∃ (δ : ℝ) (hδ : 0 < δ),
    δ < ε := by
  use ε / 2
  use half_pos hε
  exact div_two_lt_of_pos hε
```

This can also be written as follows:
```lean
example (ε : ℝ) (hε : 0 < ε) : ∃ (δ : ℝ) (hδ : 0 < δ),
    δ < ε := by
  use ε / 2, half_pos hε
  exact div_two_lt_of_pos hε
```

Again, `refine` is an abbreviation for the whole proof. Note that we have to provide a triple, cosisting of `δ`, a proof of `0 < δ`, and a proof of `δ < ε`:
```lean
example (ε : ℝ) (hε : 0 < ε) : ∃ (δ : ℝ) (hδ : 0 < δ),
    δ < ε := by
  refine ⟨ε / 2, half_pos hε, div_two_lt_of_pos hε⟩
```

:::
::::
