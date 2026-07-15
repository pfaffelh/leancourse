import Lean
import VersoManual
import Manual.Meta
import Leancourse.Misc.Defs
import Mathlib

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open MyDef

set_option pp.rawOnError true

#doc (Manual) "`simp_all`" =>
%%%
tag := "simp-all"
%%%

*Summary:* `simp_all` simplifies the goal *and every hypothesis* at once, using the hypotheses as additional simp lemmas and repeating until nothing changes. It is stronger than `simp at *`: because each simplified hypothesis feeds back in, it often closes goals that need several facts to interact.

*Example:*

::::keepEnv
:::example " "
```lean
example (p q : Prop) (h1 : p) (h2 : p → q) : q := by
  simp_all
```
:::
::::

*Notes*

* Like {ref "simp"}[`simp`], it accepts a lemma list: `simp_all [foo, bar]`.
* It can loop or be slow on many hypotheses; if so, fall back to a targeted `simp only [...] at h ⊢`.
