import Lean
import VersoManual
import Manual.Meta
import Leancourse.Misc.Defs
import Mathlib
open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open MyDef

set_option pp.rawOnError true

#doc (Manual) "`polyrith`" =>
%%%
tag := "polyrith"
%%%

*Summary:* `polyrith` *finds* a linear combination of the equality
hypotheses that proves an equality goal, by sending the problem to an
external oracle (a Sage server) over the network.  On success it
prints a concrete {ref "linear-combination"}[`linear_combination`]
call, which you then paste into your proof.

*Usage* (not run here, as it needs network access):

```
example (x y : ℝ) (h1 : x + y = 3) (h2 : x - y = 1) :
    x = 2 := by
  polyrith
-- Try this: linear_combination (h1 + h2) / 2
```

*Remarks:*

* `polyrith` requires network access and a working Python/Sage
  backend, so it may be unavailable or fail; it is a *discovery* aid,
  not something to leave in a finished proof.
* Once it suggests a combination, replace the `polyrith` call with the
  printed `linear_combination` so the proof is self-contained and
  reproducible offline.
