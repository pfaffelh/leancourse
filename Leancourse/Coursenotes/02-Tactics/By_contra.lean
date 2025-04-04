import VersoManual
import Manual.Meta
import Leancourse.Misc.Defs

open Verso.Genre Manual
open MyDef

set_option pp.rawOnError true

#doc (Manual) "`by_contra`" =>
%%%
tag := "by_contra"
%%%

**Summary**

The `by_contra` tactic provides a proof by contradiction. It is therefore assumed (i.e. transformed into a hypothesis) that the statement (after `⊢`) is not true, and this must be made to contradict itself, i.e. a proof of `false` must be found.

**Examples**

:::table (align := left) (header := true)
* + Proof state
  + Tactic
  + New proof state
* + `⊢ P`
  + `by_contra h`
  + `h : ¬P` {br}[] `⊢ False`
* + `h: ¬¬P` {br}[] `⊢ P`
  + `by_contra hnegP`
  + `h: ¬¬P` {br}[] `hnegP: ¬P` {br}[] `⊢ False`
:::

**Remarks**

This tactic is stronger than `exfalso`. After all, there the goal is only converted to `false` without adding a new hypothesis. With `by_contra`, the new goal is also `false`, but there is still a new hypothesis.

::::keepEnv
:::example " "
```lean
example (P Q : Prop) (hP: P → Q) ( hP' : ¬P → Q) : Q := by
  by_cases h : P
  · exact hP h
  · exact hP' h
```
:::
::::
