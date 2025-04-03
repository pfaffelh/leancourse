import VersoManual
import Manual.Meta
import Leancourse.Misc.Defs

open Verso.Genre Manual
open MyDef


set_option pp.rawOnError true

#doc (Manual) "`apply`" =>
%%%
tag := "apply"
%%%

**Summary:** If we have the goal `⊢ Q`, and a proof of `h : P → Q`, we only need to find a proof for `P`. This transition happens by `apply h`.

:::table (align := left) (header := true)
* + Proof state
  + Tactic
  + New proof state
* + `h : P → Q` {br}[] `⊢ Q`
  + `apply h`
  + `h : P → Q` {br}[] `⊢ P`
* + `h : ¬P` {br}[] `⊢ False`
  + `apply h`
  + `h : ¬P` {br}[] `⊢ P`
* + `h₁ : P → Q` {br}[] `h₂ : Q → R`  {br}[] `⊢ R`
  + `apply h₂ h₁`
  + `h₁ : P → Q` {br}[] `h₂ : Q → R`  {br}[] `⊢ P`
:::

The `apply`-tactics works iteratively. This means that if `apply h` makes no progress, it uses the placeholder `_` and tries to make `apply h _`.

```lean
example (hP : P) (hPQ : P → Q) (hPQR : P → Q → R) : R := by
  apply hPQR
  · sorry
  · sorry
```


**Remarks:**
* `apply` works up to equality by definition. This can be seen in the example above, where `¬P ↔ (P → False)` is true by definition.
* `apply h` is frequently identical to `refine ?_`.
* If the use of `apply` closes the current goal, you might as well use `exact` instead of `apply`.
