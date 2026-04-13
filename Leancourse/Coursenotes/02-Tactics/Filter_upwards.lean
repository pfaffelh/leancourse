import Lean
import VersoManual
import Manual.Meta
import Leancourse.Misc.Defs
import Mathlib
open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open MyDef

set_option pp.rawOnError true

#doc (Manual) "`filter_upwards`" =>
%%%
tag := "filter-upwards"
%%%

*Summary:* `filter_upwards` is the workhorse tactic for proving
goals of the form `∀ᶠ x in F, P x`.  Given a list of `Eventually`
hypotheses, it intersects them, peels off the `∀ᶠ` quantifier, and
leaves you with a pointwise goal in which all of the supplied
hypotheses appear specialized at the point `x`.

*Examples:*

:::table (align := left) +header
* + Proof state
  + Tactic
  + New proof state
* + `F : Filter α` {br}`h₁ : ∀ᶠ x in F, p x` {br}`h₂ : ∀ᶠ x in F, q x` {br}[] ⊢ ∀ᶠ x in F, p x ∧ q x
  + `filter_upwards [h₁, h₂] with x hp hq`
  + `F : Filter α` {br}`x : α` {br}`hp : p x` {br}`hq : q x` {br}[] ⊢ p x ∧ q x
:::

*Remarks:*

* The list `[h₁, h₂, ...]` may be empty (`filter_upwards []`),
  in which case the tactic only peels off the `∀ᶠ` and leaves the
  pointwise goal `P x`.
* The `with` clause names the bound point and the specialized
  hypotheses; if you omit it, fresh names are chosen automatically.
* Use `filter_upwards` whenever you want to combine several
  "eventually" facts and finish pointwise -- a very common pattern
  in analysis and measure theory (where `∀ᶠ x ∂μ` is "almost
  everywhere").
* It works for *any* filter, including `atTop`, `nhds x`, `cofinite`,
  and `μ.ae`.



::::keepEnv
:::example " "
```lean
open Filter

example {α : Type*} {F : Filter α} {p q : α → Prop}
    (hp : ∀ᶠ x in F, p x) (hq : ∀ᶠ x in F, q x) :
    ∀ᶠ x in F, p x ∧ q x := by
  filter_upwards [hp, hq] with x hp hq
  exact ⟨hp, hq⟩

-- If p holds eventually along F and ∀ x, p x → q x,
-- then q holds eventually along F.
example {α : Type*} {F : Filter α} {p q : α → Prop}
    (hp : ∀ᶠ x in F, p x) (h : ∀ x, p x → q x) :
    ∀ᶠ x in F, q x := by
  filter_upwards [hp] with x hp
  exact h x hp
```

:::
::::
