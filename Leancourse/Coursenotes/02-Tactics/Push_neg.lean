import VersoManual
import Manual.Meta
import Leancourse.Misc.Defs

open Verso.Genre Manual
open MyDef

set_option pp.rawOnError true

#doc (Manual) "`push_neg`" =>
%%%
tag := "push_neg"
%%%

**Summary:** In many steps of a proof, a negation must be carried out. In order to process the corresponding quantifiers etc. as well and to better reusable, the tactic `push_neg` is available.

**Examples**

:::table (align := left) (header := true)
* + Proof state
  + Tactic
  + New proof state
* + ⊢ ¬(P ∨ Q)
  + `push_neg`
  + ⊢ ¬P ∧ ¬Q
* + h : ¬(P ∨ Q)
  + `push_neg at h`
  + h : ¬P ∧ ¬Q
* + ⊢ ¬(P ∧ Q)
  + `push_neg`
  + ⊢ P → ¬Q
* + P : X → Prop {br}[] ⊢ ¬∀ (x : X), P x
  + `push_neg`
  + P : X → Prop {br}[] ⊢ ∃ (x : X), ¬P x
* + P : X → Prop {br}[] ⊢ ¬∃ (x : X), P x
  + `push_neg`
  + P : X → Prop {br}[] ⊢ ∀ (x : X), ¬P x
:::

::::keepEnv
:::example " "
```lean
example (P : Prop) : False → P := by
  exact False.elim
```
:::
::::

**Notes:**

This tactic also works with other objects, such as sets.
