import Lean
import VersoManual
import Manual.Meta
import Leancourse.Misc.Defs
import Mathlib
open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open MyDef

set_option pp.rawOnError true

#doc (Manual) "`norm_cast`" =>
%%%
tag := "norm-cast"
%%%

*Summary:* `norm_cast` moves coercions *outward*, out of compound
expressions and towards the root of the term.  This is the inverse
of `push_cast`, which moves coercions inward.  Together they are
the standard tools for manipulating goals that mix integer, natural,
rational, and real coercions.

*Examples:*

:::table (align := left) +header
* + Proof state
  + Tactic
  + New proof state
* + `n : ℕ` {br}[] ⊢ (n : ℝ) + (1 : ℝ) = ((n + 1 : ℕ) : ℝ)
  + `norm_cast`
  + (no goals)
:::

*Remarks:*

* Use `norm_cast` when casts sit on atoms (e.g. `(n : ℝ) + 1`) and
  you want to pull them outside.  Use `push_cast` for the opposite
  direction.
* The variant `exact_mod_cast h` applies `norm_cast` automatically
  before trying to close the goal with `h`.
* `norm_cast at h` rewrites a hypothesis.



::::keepEnv
:::example " "
```lean
example (n : ℕ) : (n : ℝ) + 1 = ((n + 1 : ℕ) : ℝ) := by
  norm_cast

example (m n : ℕ) (h : (m : ℤ) = (n : ℤ)) : m = n := by
  exact_mod_cast h
```

:::
::::
