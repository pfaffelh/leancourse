import VersoManual
import Manual.Meta
import Leancourse.Markup
import Mathlib

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open MyDef

set_option pp.rawOnError true

#doc (Manual) "`simp`" =>
%%%
tag := "simp"
%%%

*Summary:* In `mathlib` there are many lemmas with `=` or `↔` statements that can be applied with `rw` and are marked with `@[simp]`. These marked lemmas have the property that the right side is a simplified form of the left side. With `simp`, `lean` looks for matching lemmas and tries to apply them.

*Examples*

:::table (align := left) +header
* + Proof state
  + Tactic
  + New proof state
* + ⊢ n + 0 = n
  + simp
  + *no goals* 🎉
* + h : n + 0 = m {br}[] ⊢ P
  + simp at h
  + h : n = m {br}[] ⊢ P
:::

*Remarks:*

*Simp lemmas.* A lemma marked `@[simp]` is an equation `l = r` (or an `↔`) that `simp` uses from left to right, wherever `l` matches part of the goal. It repeats this until no lemma applies. The result is the *simp normal form* of the goal. A good simp lemma makes things simpler: its right side is simpler than its left, and its left side is itself in simp normal form, since otherwise `simp` would first rewrite the left side and never see the lemma match. A lemma such as `a + b = b + a`, used blindly, would loop; given such a lemma, `simp` rewrites only when the result comes earlier in a fixed order of terms. You can mark your own lemmas:

```lean
def sumSimp : ℕ → ℕ
  | 0 => 0
  | n + 1 => (n + 1) + sumSimp n

@[simp] theorem sumSimp_succ (n : ℕ) :
    sumSimp (n + 1) = (n + 1) + sumSimp n := rfl

example (n : ℕ) : sumSimp (n + 1) = n + 1 + sumSimp n := by
  simp
```

*Variants.*

:::table (align := left) +header
* + Tactic
  + Effect
* + `simp [h₁, h₂]`
  + also uses the hypotheses or lemmas `h₁`, `h₂`
* + `simp [f]`
  + also unfolds the definition `f`
* + `simp [-l]`
  + does not use the simp lemma `l`
* + `simp only [h₁, h₂]`
  + uses *only* `h₁`, `h₂`, no simp lemmas
* + `simp at h`
  + simplifies the hypothesis `h` instead of the goal
* + `simp at *`
  + simplifies all hypotheses and the goal
* + `simp_all`
  + simplifies all hypotheses and the goal, each with the others
* + `simpa using e`
  + simplifies the goal and the type of `e`, then closes the goal with `e`
* + `simp?`
  + reports the lemmas used, as a `simp only [...]` call
:::

```lean
example (a b : ℕ) (h : a = b) : a + 0 = b := by
  simp [h]

example (a b : ℕ) (h₁ : a + 0 = b) (h₂ : b = 3) :
    a = 3 := by
  simp at *
  omega
```

A `simp` without `only` in the middle of a proof is fragile: when Mathlib adds a simp lemma, the normal form changes and the following steps may break. The usual practice is to finish a goal with `simp`, or to replace it by the `simp only [...]` call that `simp?` suggests.

:::table (align := left) +header
* + Proof state
  + Tactic
  + New proof state
* + `⊢ n + 0 = n`
  + `simp?`
  + *no goals* 🎉 {br}[] Try this: {br}[]
  `simp only [add_zero]`
:::
