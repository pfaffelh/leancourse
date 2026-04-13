import Lean
import VersoManual
import Manual.Meta
import Leancourse.Misc.Defs
import Mathlib
open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open MyDef

set_option pp.rawOnError true

#doc (Manual) "`field_simp`" =>
%%%
tag := "field-simp"
%%%

*Summary:* `field_simp` clears denominators in a goal or hypothesis
involving a field (like `ℚ`, `ℝ`, `ℂ`). It rewrites expressions
of the form `a / b` into a common form, turning an equation between
rational expressions into one without division. Combined with
`ring`, it closes most identities in fields.

*Examples:*

:::table (align := left) +header
* + Proof state
  + Tactic
  + New proof state
* + `a b : ℝ` {br}`hb : b ≠ 0` {br}[] ⊢ a / b + 1 = (a + b) / b
  + `field_simp`
  + `a b : ℝ` {br}`hb : b ≠ 0` {br}[] ⊢ a + b = a + b
:::

*Remarks:*

* `field_simp` typically needs nonzeroness hypotheses for every
  denominator. These are taken from the context automatically, or
  can be supplied with `field_simp [h₁, h₂]`.
* The idiomatic combination is `field_simp; ring`: `field_simp`
  removes division, `ring` then finishes the algebraic identity.
* It works over any `Field`, `DivisionRing`, or `GroupWithZero`.



::::keepEnv
:::example " "
```lean
example (a b : ℝ) (hb : b ≠ 0) :
    a / b + 1 = (a + b) / b := by
  field_simp

example (x : ℝ) (hx : x ≠ 0) :
    (x + 1) / x - 1 / x = 1 := by
  field_simp
  ring
```

:::
::::
