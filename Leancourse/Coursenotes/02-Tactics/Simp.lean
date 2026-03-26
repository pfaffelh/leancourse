import VersoManual
import Manual.Meta
import Leancourse.Misc.Defs

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open MyDef

set_option pp.rawOnError true

#doc (Manual) "`simp`" =>
%%%
tag := "simp"
%%%

*Summary:* In `mathlib` there are many lemmas with `=` or `↔` statements that can be applied with `rw` and are marked with `@[simp]`. These marked lemmas have the property that the right side is a simplified form of the left side. With `simp`, `lean` looks for matching lemmas and tries to apply them.

*Examples*

:::table (align := left) +header
* + Proof state
  + Tactic
  + New proof state
* + ⊢ n + 0 = n
  + simp
  + *no goals* 🎉
* + h : n + 0 = m {br}[] ⊢ P
  + simp at h
  + h : n = m {br}[] ⊢ P
:::

*Remarks:*

If you want to know which lemmas were used, try `simp?`. This provides some clues.

:::table (align := left) +header
* + Proof state
  + Tactic
  + New proof state
* + `⊢ n + 0 = n`
  + `simp?`
  + *no goals* 🎉 {br}[] Try this: {br}[]
  `simp only add_zero, eq_self_iff_true`
:::

::::keepEnv
:::example " "
```lean
example (P : Prop) : False → P := by
  exact False.elim
```
:::
::::
