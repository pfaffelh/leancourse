import VersoManual
import Manual.Meta
import Leancourse.Misc.Defs

open Verso.Genre Manual
open MyDef

set_option pp.rawOnError true

#doc (Manual) "`rintro`" =>
%%%
tag := "rintro"
%%%

**Summary:** The `rintro` tactic is used to process several `intro` and `cases` tactics on one line.

**Examples**

:::table (align := left) (header := true)
* + Proof state
  + Tactic
  + New proof state
* + `⊢ P ∨ Q → R`
  + `rintro ( hP | hQ )` {br}[] = {br}[] `intro h` {br}[] `cases h with hP hQ`
  + `hP : P` {br}[] `⊢ P` {br}[] `hQ : Q` {br}[] `⊢ Q`
* + `⊢ P ∧ Q → R`
  + `rintro ⟨ hP , hQ ⟩` {br}[] = {br}[] `intro h` {br}[]  `cases h with h1 h2`
  + `hP : P` {br}[] `hQ : Q` {br}[] `⊢ R`
:::

**Notes:**

Here, more than two `∨` can also be split into cases in one step: With `A ∨ B ∨ C`, `rintro (A | B | C)` introduces three goals.

::::keepEnv
:::example " "
```lean
example (P : Prop) : False → P := by
  exact False.elim
```

{docstring Lean.Elab.Tactic.RCases.rintro}

:::
::::
