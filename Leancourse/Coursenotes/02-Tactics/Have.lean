import VersoManual
import Manual.Meta
import Leancourse.Misc.Defs
import Mathlib

open Verso.Genre Manual
open MyDef

set_option pp.rawOnError true

#doc (Manual) "`have`" =>
%%%
tag := "have"
%%%

**Summary:** By using `have` we introduce a new goal, which we have to prove first. Afterwards, it is available as a hypothesis in all further goals. This is identical to first proving a lemma `h` with the statement after `have h : ` and then reusing it at the appropriate place in the proof (for example with `apply` or `rw`).

**Examples:**

:::table (align := left) (header := true)
* + Proof state
  + Tactic
  + New proof state
* + ⊢ R
  + `have h : P ↔ Q`
  + ⊢ P ↔ Q {br}[] h : P ↔ Q {br}[] ⊢ R
* + ⊢ P
  + have h1 : ∃ (m : ℕ), f 27 m, ... {br}[] cases h1 with m hm
  + m : ℕ {br}[] hm: f 27 m {br}[] ⊢ P
:::

**Remarks:**

* Assume you want to use `have`. You could as well formulate a separate lemma and use it afterwards. It is not always clear which is better.
* If the proof of the statement is short and is only used once in your proof, you might want to consider replacing its proof in the place where it is needed.
* Suppose we have two goals (let's call them `⊢ 1` and `⊢ 2`), and we need the statement of `⊢ 1` in the proof of `⊢ 2`. We can first introduce a third goal with `have h := ⊢ 1` (where `⊢ 1` is to be replaced by the statement). Then `⊢ 1` can be proved with `exact`, and has the statement `⊢ 1` available in the proof of `⊢ 2`.

::::keepEnv
:::example " "
```lean
example (x : ℝ) (d : ℕ): 0 ≤ (d : ℝ) * x^2 := by
  have h : d ≥ 0 := by
    exact zero_le d
  have h1 : (0 : ℝ) = d * 0 := by
    simp
  rw [h1]
  apply mul_le_mul_of_nonneg_left
  nlinarith
  exact Nat.cast_nonneg' d
```

```
example (P : Prop) : False → P := by
  exact False.elim
```
:::
::::
