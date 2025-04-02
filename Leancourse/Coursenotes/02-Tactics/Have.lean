import VersoManual
import Manual.Meta
import Leancourse.Misc.Defs

open Verso.Genre Manual

set_option pp.rawOnError true

#doc (Manual) "`have`" =>
%%%
tag := "have"
%%%

**Summary:** By using `have` we introduce a new claim, which we have to prove first. Afterwards, it is available as a hypothesis in all further goals. This is identical to first proving a lemma `h` with the statement after `have h : ` and then reusing it at the appropriate place in the proof (for example with `apply` or `rw`).

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


**Notes:**

* Suppose we have two goals (let's call them `⊢1` and `⊢2`), and we need the statement of `⊢1` in the proof of `⊢2`. We can first introduce a third goal with `have h := ⊢ 1` (where `⊢1` is to be replaced by the statement). Then `⊢ 1` can be proved with `exact`, and has the statement `⊢ 1` available in the proof of `⊢ 2`.
