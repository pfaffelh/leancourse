import Lean
import VersoManual
import Manual.Meta
import Leancourse.Misc.Defs
import Mathlib
open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open MyDef

set_option pp.rawOnError true

#doc (Manual) "`set`" =>
%%%
tag := "set-tactic"
%%%

*Summary:* `set x := e` introduces a local abbreviation `x` for the
expression `e` and substitutes every occurrence of `e` in the goal
(and, with the `with` clause, in the hypotheses) with `x`.  The
substitution is definitional: `x` and `e` are interchangeable, but
the proof state becomes much more readable.

*Examples:*

:::table (align := left) +header
* + Proof state
  + Tactic
  + New proof state
* + `a b : ℕ` {br}[] `⊢ a + b + (a + b) = 2 * (a + b)`
  + `set s := a + b with hs`
  + `a b : ℕ` {br}[] `s : ℕ := a + b` {br}[] `hs : s = a + b` {br}[] `⊢ s + s = 2 * s`
:::

*Remarks:*

* Without `with hs`, no equation hypothesis is introduced, and `x`
  is still definitionally equal to `e`.
* `set` is very useful when you want to `rw` with a complicated
  subterm, or when reading the goal becomes difficult.
* The dual `let x := e` introduces a let-binding into the term but
  does *not* fold the expression in the goal.



::::keepEnv
:::example " "
```lean
example (a b : ℕ) : a + b + (a + b) = 2 * (a + b) := by
  set s := a + b with hs
  linarith
```

:::
::::
