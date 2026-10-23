import VersoManual
import Manual.Meta
import Leancourse.Markup

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open MyDef

set_option pp.rawOnError true

#doc (Manual) "`push Not`" =>
%%%
tag := "push-not"
%%%

*Summary:* In many steps of a proof, a negation must be carried out. In order to process the corresponding quantifiers etc. as well and to better reusable, the tactic `push Not` is available.

*Examples*

:::table (align := left) +header
* + Proof state
  + Tactic
  + New proof state
* + ⊢ ¬(P ∨ Q)
  + `push Not`
  + ⊢ ¬P ∧ ¬Q
* + h : ¬(P ∨ Q)
  + `push Not at h`
  + h : ¬P ∧ ¬Q
* + ⊢ ¬(P ∧ Q)
  + `push Not`
  + ⊢ P → ¬Q
* + P : X → Prop {br}[] ⊢ ¬∀ (x : X), P x
  + `push Not`
  + P : X → Prop {br}[] ⊢ ∃ (x : X), ¬P x
* + P : X → Prop {br}[] ⊢ ¬∃ (x : X), P x
  + `push Not`
  + P : X → Prop {br}[] ⊢ ∀ (x : X), ¬P x
:::

*Notes:*

This tactic also works with other objects, such as sets.
