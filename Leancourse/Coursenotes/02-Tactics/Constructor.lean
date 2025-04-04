import VersoManual
import Manual.Meta
import Leancourse.Misc.Defs

open Verso.Genre Manual
open MyDef

set_option pp.rawOnError true

#doc (Manual) "`constructor`" =>
%%%
tag := "constructor"
%%%

**Summary:** If the goal is of the type `⊢ P ∧ Q`, it is replaced by `constructor` into two goals `⊢ P` and `⊢ Q`.

**Examples**

:::table (align := left) (header := true)
* + Proof state
  + Tactic
  + New proof state
* + `⊢ P ∧ Q`
  + `constructor`
  + `⊢ P` {br}[] `⊢ Q`
* + `⊢ P ↔ Q`
  + `constructor`
  + `⊢ P → Q` {br}[] `⊢ Q → P`
:::

**Remarks**

Note that `⊢ P ↔ Q` is identical to `⊢ (P → Q) ∧ (Q → P)`.

::::keepEnv
:::example " "
```lean
example (P Q R : Prop) (hP : P) (hQ : Q)
    (hR : R) : P ∧ Q ∧ R := by
  constructor
  · exact hP
  · constructor
    · exact hQ
    · exact hR
```
In fact, `constructor` is the same as `refine ⟨?_, ?_⟩` (i.e. leaving two new goals). However, `refine` is more flexible since it is not bound to two variables:
```lean
example (P Q R : Prop) (hP : P) (hQ : Q)
    (hR : R) : P ∧ Q ∧ R := by
  refine ⟨hP, hQ, hR⟩
```

When we have a property of the natural numbers, `P : ℕ → Prop`, `{P // P m}` is the subtype which consists of all `m` for which `P m` holds. Every `(m : {P // P m})` is a pair `⟨m.val, m.prop⟩`, where `(m.val : ℕ)` is its numerical value and `m.prop` is a proof for `P m`. So, we can construct a member of the subtype by giving a number `n` and a proof `hn : P n`. The constructor `subtype_of_mem` is the constructor for the subtype `{m // P m}`. It takes a number `n` and a proof `hn : P n` and returns the pair `⟨n, hn⟩`.

```lean
def mySubtype.mk (P : ℕ → Prop) (n : ℕ) (hn : P n)
    : {m // P m} := by
  constructor
  · exact hn
```
:::
::::
