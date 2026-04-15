import Lean
import VersoManual
import Manual.Meta
import Leancourse.Misc.Defs
import Mathlib
open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open MyDef

set_option pp.rawOnError true

#doc (Manual) "`show`" =>
%%%
tag := "show"
%%%

*Summary:* `show e` changes the syntactic form of the current goal
to `e`, provided `e` is *definitionally equal* to the goal.  It is
the tactic counterpart of the term-mode `(h : T)` ascription.

*Examples:*

:::table (align := left) +header
* + Proof state
  + Tactic
  + New proof state
* + `⊢ 1 + 1 = 2`
  + `show 2 = 2`
  + `⊢ 2 = 2`
* + `⊢ P ∨ Q`
  + `show Q ∨ P`
  + `(fails: not def-equal)`
:::

*Remarks:*

* `show` does not prove anything; it only reshapes the goal.  It is
  useful before `rw`, `apply`, or `exact` when those tactics expect
  a specific syntactic shape.
* `show e` fails if `e` is not definitionally equal to the goal.
  For propositional reshaping (which is not definitional) use
  `change` or `suffices`.



::::keepEnv
:::example " "
```lean
example : 1 + 1 = 2 := by
  show 2 = 2
  rfl

example (n : ℕ) : n + 0 = n := by
  show n = n
  rfl
```

:::
::::
