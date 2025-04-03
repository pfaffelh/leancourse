import VersoManual
import Manual.Meta
import Leancourse.Misc.Defs

open Verso.Genre Manual
open MyDef

set_option pp.rawOnError true

#doc (Manual) "`linarith`" =>
%%%
tag := "linearith"
%%%

**Summary:** This tactic can prove equations and inequalities with the help of hypotheses. It is important that the hypotheses used are also only equations and inequalities. So here we are working mainly with the transitivity of `<` together with arithmetic rules.

**Examples:**

:::table (align := left) (header := true)
* + Proof state
  + Tactic
  + New proof state
* + `h₁ : a < b` {br}[] `h₂ : b < c` {br}[] ⊢ a < c
  + linarith
  + **no goals**
:::
