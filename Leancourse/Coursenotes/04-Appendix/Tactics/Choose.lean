import Lean
import VersoManual
import Manual.Meta
import Leancourse.Misc.Defs
import Mathlib

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open MyDef

set_option pp.rawOnError true

#doc (Manual) "`choose`" =>
%%%
tag := "choose"
%%%

*Summary:* `choose f hf using h` turns a hypothesis `h : ∀ x, ∃ y, P x y` into a *function* `f` together with `hf : ∀ x, P x (f x)`. It is the tactic form of *choosing a witness for every input at once* -- indispensable when you need to build a sequence or function from a family of existence statements (a constant move in analysis). It handles several `∀`/`∃` layers and extra conclusions in one call.

*Example:*

::::keepEnv
:::example " "
```lean
example (h : ∀ n : ℕ, ∃ m : ℕ, n < m) :
    ∃ f : ℕ → ℕ, ∀ n, n < f n := by
  choose f hf using h
  exact ⟨f, hf⟩
```
:::
::::

*Notes*

* For a *single* existential, {ref "obtain"}[`obtain ⟨y, hy⟩ := h`] is enough; `choose` is what you want when the witness must depend on a *bound* variable.
* `choose!` additionally cleans up trivial hypotheses.
