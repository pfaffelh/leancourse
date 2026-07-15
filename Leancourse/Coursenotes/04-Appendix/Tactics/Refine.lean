import VersoManual
import Manual.Meta
import Leancourse.Misc.Defs

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open MyDef

set_option pp.rawOnError true

#doc (Manual) "`refine`" =>
%%%
tag := "refine"
%%%

*Summary:* `refine` is `exact` with *holes*: you give the proof term but leave some parts open, and each hole comes back as a new goal. Write a hole as `?_` for an explicit new goal; a plain `_` instead asks Lean to *infer* that part, and only turns into a goal if it cannot. This makes `refine` the tool for building a proof term *outside-in* -- state its shape now, discharge the pieces as separate goals. A *named* hole `?h` labels its goal `case h`, which is convenient when several are open.

The most common use is to *split* a goal by naming the constructor or lemma that produces it and leaving its arguments as holes -- an anonymous constructor `⟨…⟩` for an `∧`, `↔`, `∃`, structure, or subtype, or a lemma such as `le_antisymm` for an equality.

*Examples:*

:::table (align := left) +header
* + Proof state
  + Tactic
  + New proof state
* + `hQ : Q` {br}[] `⊢ P ∧ Q`
  + `refine ⟨?_, hQ⟩`
  + `hQ : Q` {br}[] `⊢ P`
* + `⊢ P ↔ Q`
  + `refine ⟨?_, ?_⟩`
  + `⊢ P → Q` {br}[] `⊢ Q → P`
* + `a b : ℝ` {br}[] `⊢ a = b`
  + `refine le_antisymm ?_ ?_`
  + `⊢ a ≤ b` {br}[] `⊢ b ≤ a`
* + `⊢ ∃ n : ℕ, n > 0`
  + `refine ⟨5, ?_⟩`
  + `⊢ 5 > 0`
* + `hP : P` {br}[] `⊢ P ∧ Q ∧ R`
  + `refine ⟨hP, ?_, ?_⟩`
  + `⊢ Q` {br}[] `⊢ R`
* + `⊢ P ∧ Q`
  + `refine ⟨?hP, ?hQ⟩`
  + `case hP ⊢ P` {br}[] `case hQ ⊢ Q`
* + `⊢ ∃ (n : ℕ) (h : n > 0), n ^ 2 = 9`
  + `refine ⟨3, ?_, by norm_num⟩`
  + `⊢ 3 > 0`
:::

::::keepEnv
:::example " "
```lean
example (P Q : Prop) (hP : P) (hQ : Q) : P ∧ Q := by
  refine ⟨?_, ?_⟩
  · exact hP
  · exact hQ
```
:::
::::
