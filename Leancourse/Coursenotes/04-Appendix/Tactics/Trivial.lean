import Lean
import VersoManual
import Manual.Meta
import Leancourse.Misc.Defs
import Mathlib
open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open MyDef

set_option pp.rawOnError true

#doc (Manual) "`trivial`" =>
%%%
tag := "trivial"
%%%

*Summary:* `trivial` tries a short list of simple tactics to close
the goal: `rfl`, `assumption`, `True.intro`, `decide`, and a few
others.  It is a gentle hammer for goals that "should be obvious".

*Examples:*

:::table (align := left) +header
* + Proof state
  + Tactic
  + New proof state
* + `⊢ True`
  + `trivial`
  + (no goals)
* + `h : P` {br}[] ⊢ P
  + `trivial`
  + (no goals)
:::

*Remarks:*

* Unlike `triv`, `trivial` also closes goals that are true by
  decidability (like `2 + 2 = 4`).
* When `trivial` does not close a goal, it prints no specific
  reason -- if you want a more informative automated tactic, try
  `exact?` or `simp`.



::::keepEnv
:::example " "
```lean
example : True := by trivial
example (P : Prop) (h : P) : P := by trivial
example : (2 + 2 : ℕ) = 4 := by trivial
```

:::
::::
