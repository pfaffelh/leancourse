import Lean
import VersoManual
import Manual.Meta
import Leancourse.Misc.Defs
import Mathlib

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open MyDef

set_option pp.rawOnError true

#doc (Manual) "`wlog`" =>
%%%
tag := "wlog"
%%%

*Summary:* `wlog h : P with H` formalizes *"without loss of generality, assume `P`"*. It produces two goals:

* a *reduction* goal, where you are handed `H` -- the full statement, generalized over the relevant variables -- and must prove the goal *in general*, typically by applying `H` to a swapped/symmetric instance to cover the case `¬P`;
* the *main* goal, where you may now assume `h : P`.

*Example:* commutativity of `+`, reduced to the case `a ≤ b`:

::::keepEnv
:::example " "
```lean
example (a b : ℕ) : a + b = b + a := by
  wlog h : a ≤ b with H
  · exact (H b a (not_le.mp h).le).symm
  · omega
```
:::
::::

*Notes*

* `wlog` pays off when discharging `¬P` really is symmetric to `P`; if it is not, you have not actually saved work.
