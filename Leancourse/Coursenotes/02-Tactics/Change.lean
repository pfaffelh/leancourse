import VersoManual
import Manual.Meta
import Leancourse.Misc.Defs

open Verso.Genre Manual
open MyDef

set_option pp.rawOnError true

#doc (Manual) "`change`" =>
%%%
tag := "change"
%%%

Changes the goal (or a hypothesis) into a goal (or a hypothesis) that is defined the same.

**Examples:**

:::table (align := left) (header := true)
* + Proof state
  + Tactic
  + New proof state
* + ⊢ : P → false
  + change ¬P
  + ⊢ ¬P
* + h : ¬P {br}[] ⊢ Q
  + change P → false at h
  + h: P → false {br}[] ⊢ Q
* + xs : x ∈ s {br}[] ⊢ x ∈ f ⁻¹' (f '' s)
  + change f x ∈ f '' s
  + xs : x ∈ s {br}[] ⊢ f x ∈ f '' s
:::

**Notes:**

* As can be seen from the penultimate example, `change` also works for hypotheses.
* Since many tactics test for definitional equality anyway, `change` is often not necessary. However, it can help to make the proof more readable.
