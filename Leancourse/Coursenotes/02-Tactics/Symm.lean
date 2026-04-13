import Lean
import VersoManual
import Manual.Meta
import Leancourse.Misc.Defs
import Mathlib
open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open MyDef

set_option pp.rawOnError true

#doc (Manual) "`symm`" =>
%%%
tag := "symm"
%%%

*Summary:* `symm` swaps the two sides of a symmetric relation.
For equality, it turns a goal `a = b` into `b = a`.  It also works
for `↔`, `≃`, `Dvd.dvd`, and any other relation tagged `@[symm]`
in Mathlib.

*Examples:*

:::table (align := left) +header
* + Proof state
  + Tactic
  + New proof state
* + `a b : ℕ` {br}[] ⊢ a = b
  + `symm`
  + `a b : ℕ` {br}[] ⊢ b = a
* + `h : a = b` {br}[] ⊢ ...
  + `symm at h`
  + `h : b = a` {br}[] ⊢ ...
:::

*Remarks:*

* The term-mode analogue is `Eq.symm h` (or `.symm`).
* `symm` is often used just before `exact h` when you have `h : b = a`
  but a goal `a = b`.



::::keepEnv
:::example " "
```lean
example (a b : ℕ) (h : a = b) : b = a := by
  symm
  exact h

example (P Q : Prop) (h : P ↔ Q) : Q ↔ P := by
  symm
  exact h
```

:::
::::
