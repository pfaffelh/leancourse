import Lean
import VersoManual
import Manual.Meta
import Leancourse.Misc.Defs
import Mathlib
open Verso.Genre Manual
open MyDef

set_option pp.rawOnError true

#doc (Manual) "`ext`" =>
%%%
tag := "ext"
%%%

**Summary:** Extensionality is a principle that states that two functions are equal if they give the same result for all arguments. The `ext` tactic applies this principle to prove the equality of two functions.

**Examples:**

:::table (align := left) (header := true)
* + Proof state
  + Tactic
  + New proof state
* + `f g : ℝ → ℝ` {br}[] ⊢ f = g
  + `ext x`
  + `f g : ℝ → ℝ` {br}`x : ℝ` {br}[] ⊢ f x = g x
:::

**Remarks:**

* Extensionality works for functions and sets.



::::keepEnv
:::example " "
```lean
example (f g : ℝ → ℝ) (hf : f = fun x ↦ x + x)
    (hg : g = fun x ↦ 2 * x): f = g := by
  rw [hf, hg]
  ext x
  rw [← two_mul x]

example (s t : Set ℝ) (hs : ∀ x ∈ s, x ∈ t) (ht : t ⊆ s):
    s = t  := by
  ext x
  refine ⟨hs x, fun a => ht (hs x (ht a))⟩
```

#moogle "induction"


{docstring Lean.Nat.induction}

:::
::::
