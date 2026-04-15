import Lean
import VersoManual
import Manual.Meta
import Leancourse.Misc.Defs
import Mathlib
open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open MyDef

set_option pp.rawOnError true

#doc (Manual) "`contradiction`" =>
%%%
tag := "contradiction"
%%%

*Summary:* `contradiction` closes the goal if the local context
contains two contradictory hypotheses, or a hypothesis of type
`False`, or `h : a ≠ a`, or similar trivially absurd facts.

*Examples:*

:::table (align := left) +header
* + Proof state
  + Tactic
  + New proof state
* + `h : False` {br}`⊢ P`
  + `contradiction`
  + (no goals)
* + `h₁ : P` {br}`h₂ : ¬P` {br}`⊢ Q`
  + `contradiction`
  + (no goals)
:::

*Remarks:*

* `contradiction` is usually faster and cleaner than `exact absurd h h'`
  or `exfalso; exact h' h`.
* It also recognises `Nat.zero_ne_one`-style contradictions and
  evaluates numeric literals.



::::keepEnv
:::example " "
```lean
example (h : False) (P : Prop) : P := by
  contradiction

example (P Q : Prop) (h₁ : P) (h₂ : ¬P) : Q := by
  contradiction

example (h : (0 : ℕ) = 1) (P : Prop) : P := by
  contradiction
```

:::
::::
