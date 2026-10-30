import Lean
import VersoManual
import Manual.Meta
import Leancourse.Markup
import Mathlib
open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open MyDef

set_option pp.rawOnError true

#doc (Manual) "`classical`" =>
%%%
tag := "classical"
%%%

*Summary:* `classical` makes every proposition decidable for the rest
of the proof. It registers `Classical.propDecidable` as a local
instance with low priority, so that `if P then … else …`,
`Finset.filter P` and `Finset.image` work for any `P` and any type.
The goal does not change.

*Examples:*

:::table (align := left) +header
* + Proof state
  + Tactic
  + New proof state
* + `P : ℕ → Prop` {br}[] `s : Finset ℕ` {br}[] `⊢ ∃ t ⊆ s, ∀ x ∈ t, P x`
  + `classical`
  + `P : ℕ → Prop` {br}[] `s : Finset ℕ` {br}[] `⊢ ∃ t ⊆ s, ∀ x ∈ t, P x`
:::

The goal is the same, but afterwards `s.filter P` is accepted as a
witness. Without `classical` it fails with
`failed to synthesize DecidablePred P`.

*Remarks:*

* `classical` acts only on the proof. If the *statement* needs an
  instance, as `(s.image f).card ≤ s.card` needs `DecidableEq β`, put
  `[DecidableEq β]` among the hypotheses.
* For a definition, write `open Classical in` in front of it; the
  definition is then `noncomputable`.
* `by_cases` does not need `classical`.
* Instances that exist, such as decidable equality on `ℕ`, are still
  found first. See {ref "classical-tactic"}[The `classical` tactic] in
  the typeclass chapter.

::::keepEnv
:::example " "
```lean
example (P : ℕ → Prop) (s : Finset ℕ) :
    ∃ t ⊆ s, ∀ x ∈ t, P x := by
  classical
  refine ⟨s.filter P, Finset.filter_subset P s, ?_⟩
  intro x hx
  exact (Finset.mem_filter.mp hx).2
```

:::
::::
