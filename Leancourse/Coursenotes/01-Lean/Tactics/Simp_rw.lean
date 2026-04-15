import Lean
import VersoManual
import Manual.Meta
import Leancourse.Misc.Defs
import Mathlib
open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open MyDef

set_option pp.rawOnError true

#doc (Manual) "`simp_rw`" =>
%%%
tag := "simp-rw"
%%%

*Summary:* `simp_rw [h₁, h₂, ...]` rewrites with each lemma in turn,
but -- unlike `rw` -- can rewrite *under binders* (`∀`, `∃`, `fun`,
`∑`, ...).  Unlike `simp`, it does not apply any extra simp lemmas;
it rewrites with exactly the lemmas you supply.

*Examples:*

:::table (align := left) +header
* + Proof state
  + Tactic
  + New proof state
* + `f : ℕ → ℕ` {br}`h : ∀ n, f n = 0` {br}`⊢ ∀ n, f n + 1 = 1`
  + `simp_rw [h]`
  + `⊢ ∀ n, 0 + 1 = 1`
:::

*Remarks:*

* `rw` refuses to rewrite under binders, giving a "motive is not
  type correct" error in those situations.  `simp_rw` is the right
  tool there.
* If the lemmas you rewrite with are simp lemmas *and* you are happy
  for simp to apply other simp lemmas too, just use `simp only`.



::::keepEnv
:::example " "
```lean
example (f : ℕ → ℕ) (h : ∀ n, f n = 0) :
    ∀ n, f n + 1 = 1 := by
  simp_rw [h]
  intro n
  simp
```

:::
::::
