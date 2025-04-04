import VersoManual
import Manual.Meta
import Leancourse.Misc.Defs

open Verso.Genre Manual
open MyDef

set_option pp.rawOnError true

#doc (Manual) "`intro`" =>
%%%
tag := "intro"
%%%

**Summary**

If the goal is of the form `⊢ P → Q` or `∀ (n : ℕ), P n`, you can proceed with `intro P` or `intro n`. You can use several `intro` commands at the same time to summarize a single one. A little more precisely, `intro h1 h2 h3,` is identical to `intro h1; intro h2; intro h3`.


**Examples**

:::table (align := left) (header := true)
* + Proof state
  + Tactic
  + New proof state
* + ⊢ P → Q
  + intro hP
  + hP : P {br}[] ⊢ Q
* + f : α → Prop {br}[] ⊢ ∀ (x : α), f x
  + intro x
  + f: α → Prop {br}[] x : α {br}[] ⊢ f x
* + ⊢ P → Q → R
  + intro hP hQ
  + hP : P {br}[] hQ : Q {br}[] ⊢ R
* + P : ℕ → Prop {br}[] ⊢ ∀ (n : ℕ), P n → Q
  + intro n hP
  + P : ℕ → Prop {br}[] n : ℕ {br}[] hP: P n ⊢ Q
:::

::::keepEnv
:::example " "
```lean
example (P : Prop) : False → P := by
  exact False.elim
```
:::
::::

**Remarks**

* Several `intro` commands in a row are best combined. Furthermore,  `rintro` is a more flexible variant.
* A reversal of `intro` is `revert`.
