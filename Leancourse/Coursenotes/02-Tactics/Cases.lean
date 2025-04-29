import VersoManual
import Manual.Meta
import Leancourse.Misc.Defs

open Verso.Genre Manual
open MyDef

set_option pp.rawOnError true

#doc (Manual) "`cases'`" =>
%%%
tag := "cases"
%%%

**Summary:** If a hypothesis is composed, i.e. can be expanded into two or more cases, `cases'` delivers exactly that. This can be used not only used with hypotheses `h : P ∨ Q` or `h : P ∧ Q`, but also with structures that consist of several cases, such as `∃...` (here there is a variable and a statement) and `x : bool` or `n : ℕ`.

**Examples:**


:::table (align := left) (header := true)
* + Proof state
  + Tactic
  + New proof state
* + h : P ∧ Q
  + cases h with hP hQ
  + hP : P {br}[] hQ : Q {br}[] ⊢ R
* + h : P ∨ Q
  + cases h with hP hQ
  + hP : P {br}[] ⊢ R {br}[] hQ : Q {br}[]⊢ R
* + h : False {br}[] ⊢ P
  + cases h
  + **no goals🎉**
* + P: ℕ → Prop {br}[] h: ∃ (m : ℕ), P m {br}[] ⊢ Q
  + cases x with m h1
  + P : ℕ → Prop {br}[] m : ℕ {br}[] h1 : P m {br}[] ⊢ Q
* + x : Bool {br}[] ⊢ x = True ∨ x = False
  + cases x
  + ⊢ False = True ∨ False = False {br}[] ⊢ True = True ∨ True = False
* + n : ℕ {br}[] ⊢ n > 0 → (∃ (k : ℕ), n = k + 1)
  + cases n
  + ⊢ 0 > 0 → (∃ (k : ℕ), 0 = k + 1) {br}[] ⊢ n.succ > 0 → (∃ (k : ℕ),
n.succ = k + 1)
:::


**Remarks:**

* The application `cases' n` for `n : ℕ` is strictly weaker than complete induction (see `induction`). After all, `cases` only converts `n : ℕ` into the two cases `0` and `succ n`, but you cannot use the statement for `n-1` to prove the statement for `n`.
* A more flexible version of `cases'` is `rcases`.

::::keepEnv
:::example " "
```lean
example (P Q : Prop) (hP: P → Q) ( hP' : ¬P → Q) : Q := by
  by_cases h : P
  · exact hP h
  · exact hP' h
```

:::
::::
