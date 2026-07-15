import Lean
import VersoManual
import Manual.Meta
import Leancourse.Misc.Defs
import Mathlib

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open MyDef

set_option pp.rawOnError true

#doc (Manual) "`trans`" =>
%%%
tag := "trans"
%%%

*Summary:* `trans b` proves a *transitive* goal `a R c` -- for `=`, `≤`, `<`, `⊆`, `∣`, and any relation with a registered `Trans` instance -- by splitting it into the two goals `a R b` and `b R c` for a middle term `b` you supply. It is the transitivity counterpart of {ref "symm"}[`symm`].

*Example:*

::::keepEnv
:::example " "
```lean
example (a b c : ℕ) (h1 : a ≤ b) (h2 : b ≤ c) : a ≤ c := by
  trans b
  · exact h1
  · exact h2
```
:::
::::

*Notes*

* For a chain of many steps, {ref "calc"}[`calc`] is usually more readable than nested `trans`.
