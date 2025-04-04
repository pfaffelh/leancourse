import VersoManual
import Manual.Meta
import Leancourse.Misc.Defs

open Verso.Genre Manual
open MyDef

set_option pp.rawOnError true

#doc (Manual) "`rcases`" =>
%%%
tag := "rcases"
%%%

:::table (align := left) (header := true)
* + Proof state
  + Tactic
  + New proof state
* + `h : P ∧ Q ∨ P ∧ R` {br}[] ⊢ P
  + `rcases h with (⟨hP1,hQ⟩|⟨hP2,hR⟩)`
  + hP1 : P {br}[] hQ : Q {br}[] ⊢ P {br}[] hP2 : P{br}[] hR : R {br}[] ⊢ P
:::

**Summary:** `rcases` is a more flexible version of `cases`. Here, it is allowed to use `⟨ hP, hQ ⟩` (or `(hP | hQ)`) to to split the hypotheses `hP` and `hQ` into their cases.  As can be seen in the example above, it is also possible to nest `⟨.,.⟩` and `(.|.)`.

**Examples:**

:::table (align := left) (header := true)
* + Proof state
  + Tactic
  + New proof state
* + `h : P ∧ Q` {br}[] `⊢ R`
  + `rcases h with`⟨ hP, hQ ⟩`
  + `hP : P`  {br}[] `hQ : Q`  {br}[] `⊢ R`
* + `h : P ∨ Q` {br}[] `⊢ R`
  + `rcases h with`( hP | hQ )`
  + `hP : P`  {br}[] `⊢ R` {br}[] `hQ : Q` {br}[] `⊢ R`
* + `h : ∃ (m : ℕ) (hg : 0 ≤ m), m < n` {br}[] `⊢ P`
  + `rcases h with⟨m, h1, h2⟩`
  + `n m : ℕ` {br}[] `h1 : 0 ≤ m` {br}[] `h2 : m < n`  {br}[] `⊢ 1 < n`
:::

::::keepEnv
:::example " "
```lean
example (P : Prop) : False → P := by
  exact False.elim
```
:::
::::

**Notes:**

The last example shows how to use `rcases` to directly resolve a ∃ quantifier in a hypothesis that has more than one constraint (here: 0 ≤ m) and m < n can be resolved directly.
