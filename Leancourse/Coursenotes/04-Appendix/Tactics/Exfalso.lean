import VersoManual
import Manual.Meta
import Leancourse.Misc.Defs

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open MyDef

set_option pp.rawOnError true

#doc (Manual) "`exfalso`" =>
%%%
tag := "exfalso"
%%%

*Summary:* The statement `False → P` is true for all `P`. If the current goal is `⊢ P`, and you would apply this true statement using `apply`, the new goal would be `⊢ False`. This is exactly what the `exfalso` tactic does.

*Examples:*

:::table (align := left) +header
* + Proof state
  + Tactic
  + New proof state
* + `h : P` {br}[] ⊢ Q
  + `exfalso`
  + `h : P` {br}[] ⊢ False
* + hP : P {br}[] hnP : ¬P {br}[] ⊢ Q
  + exfalso
  + hP : P {br}[] hnP: ¬P {br}[] ⊢ False
:::

*Remarks:*

* `exfalso` is constructive: *ex falso quodlibet* is a rule of intuitionistic logic and needs no excluded middle. It is the recursor of `False`, which has no constructor and hence no case to supply; see {ref "true-false"}[`True` and `False`].
* `exfalso` is the same as `apply False.elim`; see the examples for {ref "exact"}[`exact`].

::::keepEnv
:::example " "
```lean
example (P : Prop) : False → P := by
  exact False.elim
```
:::
::::
