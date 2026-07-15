import VersoManual
import Manual.Meta
import Leancourse.Misc.Defs

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open MyDef

set_option pp.rawOnError true

#doc (Manual) "`left`" =>
%%%
tag := "left"
%%%

*Summary:*

If the goal is a disjunction `⊢ P ∨ Q`, then `left` reduces it to `⊢ P` -- it is exactly `apply Or.inl`, so it suffices to prove the left disjunct. Symmetrically, {ref "right"}[`right`] reduces `⊢ P ∨ Q` to `⊢ Q` (`apply Or.inr`). More generally, for any goal whose type is an inductive with two constructors, `left` picks the *first* constructor and `right` the *second*.

*Examples:*

:::table (align := left) +header
* + Proof state
  + Tactic
  + New proof state
* + `⊢ P ∨ Q`
  + `left`
  + `⊢ P`
* + `⊢ P ∨ Q`
  + `right`
  + `⊢ Q`
:::

::::keepEnv
:::example " "
```lean
example (P Q : Prop) (hP : P) : P ∨ Q := by
  left
  exact hP
```
:::
::::

*Remarks:*

* See also {ref "right"}[`right`], the symmetric choice (`apply Or.inr`).
* `left` and `right` apply to any goal that is a two-constructor inductive type, not only `∨`; on `∨` they are the everyday "prove the left / right disjunct".
