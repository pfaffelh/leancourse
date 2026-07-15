import VersoManual
import Manual.Meta
import Leancourse.Misc.Defs
import Mathlib

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open MyDef

set_option pp.rawOnError true

#doc (Manual) "`conv`" =>
%%%
tag := "conv"
%%%

*Summary:* `rw` and `simp` rewrite the *first* matching subterm (and every copy of it), which is sometimes the wrong place -- and neither can reach *under a binder* such as `∀`, `∃`, or `∑`. The `conv` tactic enters *conversion mode*: you first *navigate* to the exact subterm you mean, and only then rewrite it. Once focused, `rw`, `simp`, and `change` act *only* on the focused subterm.

Navigation inside `conv => …`:

* `lhs` / `rhs` -- move into the left / right operand of an `=`, `↔`, or binary operation.
* `enter [i, j, …]` -- descend into argument `i`, then `j`, … of the focused term.
* `ext x` -- go *under* a binder, introducing `x`; this is what lets you rewrite beneath `∀`/`λ`/`∑`.
* `conv at h => …` operates inside a hypothesis `h` instead of the goal.
* the shorthands `conv_lhs => …` and `conv_rhs => …` start already focused on one side of the goal.

*Examples:*

:::table (align := left) +header
* + Goal (with `h`)
  + Tactic
  + Effect
* + `h : a = b` {br}[] `⊢ a + a = b + a`
  + `conv_lhs => lhs; rw [h]`
  + rewrites only the *first* `a`
* + `h : ∀ n, f n = 0` {br}[] `⊢ (fun n => f n) = 0`
  + `conv_lhs => ext n; rw [h]`
  + rewrites *under* the `λ`
* + `h : a + 0 = b`
  + `conv at h => lhs; rw [add_zero]`
  + turns `h` into `a = b`
:::

::::keepEnv
:::example " "
```lean
-- rw [h] would rewrite BOTH a's; conv hits only the first
example (a b : ℕ) (h : a = b) : a + a = b + a := by
  conv_lhs => lhs; rw [h]
```
:::
::::

::::keepEnv
:::example "Rewriting under a binder"
`rw` cannot rewrite beneath a `λ` or `∀`; `conv … ext` can (as can `simp only`).
```lean
example (f : ℕ → ℕ) (h : ∀ n, f n = 0) :
    (fun n => f n + 1) = (fun n => 0 + 1) := by
  conv_lhs => ext n; rw [h]
```
:::
::::

*Notes*

* `conv` changes the goal (or hypothesis) into a *definitionally equal* one, exactly like `rw`; it just gives you control over *where*.
* When you only need "the second occurrence", {ref "nth_rewrite"}[`nth_rewrite`] is often shorter than a full `conv` block.
