import Lean
import VersoManual
import Manual.Meta
import Leancourse.Misc.Defs
import Mathlib

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open MyDef

set_option pp.rawOnError true

#doc (Manual) "`unfold`" =>
%%%
tag := "unfold"
%%%

*Summary:* `unfold f` replaces the constant `f` by its definition in the goal (`unfold f at h` in a hypothesis). It works on `def`s by rewriting with their *equation lemmas*, so it also unfolds functions defined by pattern matching.

*Example:*

::::keepEnv
:::example " "
```lean
def myDbl (n : ℕ) : ℕ := 2 * n

-- `ring` cannot see through `myDbl`; unfold it first
example (n : ℕ) : myDbl n = n + n := by
  unfold myDbl
  ring
```
:::
::::

*Notes*

* If the two sides are already {ref "defeq"}[definitionally equal] after unfolding, {ref "rfl"}[`rfl`] alone often suffices -- `unfold` just makes the step explicit.
* `simp only [myDbl]` unfolds via the same equation lemmas and is frequently more robust; `show` or {ref "change"}[`change`] can also replace the goal with an unfolded, definitionally-equal form.
