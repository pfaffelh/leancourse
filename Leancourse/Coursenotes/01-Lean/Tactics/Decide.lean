import Lean
import VersoManual
import Manual.Meta
import Leancourse.Misc.Defs
import Mathlib
open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open MyDef

set_option pp.rawOnError true

#doc (Manual) "`decide`" =>
%%%
tag := "decide"
%%%

*Summary:* `decide` closes a goal whose statement is *decidable* --
i.e. the typeclass `Decidable P` finds a proof or refutation of `P`
by computation.  Typical candidates are concrete arithmetic
equalities and inequalities, membership in a finite set, divisibility,
and propositional logic on concrete inputs.

*Examples:*

:::table (align := left) +header
* + Proof state
  + Tactic
  + New proof state
* + `⊢ (2 + 2 : ℕ) = 4`
  + `decide`
  + (no goals)
* + `⊢ (3 : ℕ) ∣ 12`
  + `decide`
  + (no goals)
:::

*Remarks:*

* `decide` performs *reduction*: it reduces the decision procedure
  on the given inputs.  For large inputs it can be slow (or time
  out); for general arithmetic, prefer `omega` or `norm_num`.
* For propositions that depend on a variable (e.g. `∀ n, P n`),
  `decide` will not work -- it needs concrete inputs.



::::keepEnv
:::example " "
```lean
example : (2 + 2 : ℕ) = 4 := by decide
example : (3 : ℕ) ∣ 12 := by decide
example : ¬ ((10 : ℕ) = 20) := by decide
```

:::
::::
