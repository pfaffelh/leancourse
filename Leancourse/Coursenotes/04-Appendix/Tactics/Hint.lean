import Lean
import VersoManual
import Manual.Meta
import Leancourse.Misc.Defs
import Mathlib

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open MyDef

set_option pp.rawOnError true

#doc (Manual) "`hint`" =>
%%%
tag := "hint"
%%%

*Summary:* `hint` runs a curated list of standard tactics -- among them `simp`, `exact?`, `omega`, `linarith`, `decide`, `tauto` -- on the current goal and reports in the infoview which of them close it. It does *not* change the proof state; it is a *suggestion* tool. When you are stuck and unsure what to try, `hint` is often the fastest way to find a one-line finish.

*Example:*

```
example (a b : ℕ) (h : a ≤ b) : a ≤ b + 1 := by
  hint      -- infoview: "Try these:" omega, linarith, …
  omega     -- then apply one of the suggestions
```

*Notes*

* Because `hint` only reports, you still write the chosen tactic yourself -- unlike {ref "apply-qm"}[`apply?`]/`exact?`, which offer an exact term to insert.
* The list of tactics `hint` tries is configurable, but the defaults cover the common cases.
