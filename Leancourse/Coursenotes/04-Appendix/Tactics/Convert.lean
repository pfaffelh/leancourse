import Lean
import VersoManual
import Manual.Meta
import Leancourse.Misc.Defs
import Mathlib

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open MyDef

set_option pp.rawOnError true

#doc (Manual) "`convert`" =>
%%%
tag := "convert"
%%%

*Summary:* `convert e` closes the goal with `e` *up to congruence*: it matches the goal against the type of `e` and leaves the *mismatched subterms* as new equality goals. Reach for it when you have a proof of something that is *almost* the goal -- the two differ only in a few places. `convert e using n` limits how deep the matching descends: stopping after `n` layers gives fewer but larger leftover goals.

*Example:*

::::keepEnv
:::example " "
```lean
-- `h` proves almost the goal; the summands differ
example (a b : ℕ) (hab : a = b) (h : a + a = 4) :
    b + b = 4 := by
  convert h using 2 <;> exact hab.symm
```
:::
::::

*Notes*

* Without `using`, `convert` descends as far as it can, which sometimes produces many tiny goals; add `using 1` or `using 2` to stop earlier.
* `convert` is the congruence-aware cousin of {ref "exact"}[`exact`]; when the two sides differ only by *rewriting*, {ref "rw"}[`rw`] is usually cleaner.
