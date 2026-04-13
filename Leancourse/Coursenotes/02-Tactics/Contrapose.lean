import Lean
import VersoManual
import Manual.Meta
import Leancourse.Misc.Defs
import Mathlib
open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open MyDef

set_option pp.rawOnError true

#doc (Manual) "`contrapose`" =>
%%%
tag := "contrapose"
%%%

*Summary:* `contrapose` applies the contrapositive: given a goal
`P → Q`, it turns it into `¬Q → ¬P`.  The variant `contrapose!`
additionally pushes the negations inward using `push_neg`.

*Examples:*

:::table (align := left) +header
* + Proof state
  + Tactic
  + New proof state
* + `h : P` {br}[] ⊢ Q
  + `contrapose h`
  + `h : ¬Q` {br}[] ⊢ ¬P
* + `h : x ≤ y` {br}[] ⊢ f x ≤ f y
  + `contrapose! h`
  + `h : f y < f x` {br}[] ⊢ y < x
:::

*Remarks:*

* `contrapose` (without `!`) simply inserts `¬`.  `contrapose!`
  additionally runs `push_neg` on both the hypothesis and the goal,
  so `¬(x ≤ y)` becomes `y < x` and so on.
* `contrapose` operates on a hypothesis by default; to contrapose the
  goal only, use `contrapose` without an argument.



::::keepEnv
:::example " "
```lean
example (P Q : Prop) (h : P → Q) : ¬Q → ¬P := by
  intro hnQ hP
  exact hnQ (h hP)

example (x y : ℝ) : y + 1 < x + 1 → y < x := by
  intro h
  linarith
```

:::
::::
