import Lean
import VersoManual
import Manual.Meta
import Leancourse.Misc.Defs
import Mathlib
open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open MyDef

set_option pp.rawOnError true

#doc (Manual) "`funext`" =>
%%%
tag := "funext"
%%%

*Summary:* `funext` is the *function extensionality* tactic. To
prove a goal of the form `f = g`, where `f g : (x : α) → β x` are
two (possibly dependent) functions, `funext x` introduces a fresh
variable `x : α` and reduces the goal to `f x = g x`.  This
relies on the `funext` axiom from Lean's type theory.

*Examples:*

:::table (align := left) +header
* + Proof state
  + Tactic
  + New proof state
* + `f g : ℕ → ℕ` {br}[] ⊢ f = g
  + `funext n`
  + `f g : ℕ → ℕ` {br}`n : ℕ` {br}[] ⊢ f n = g n
* + `f g : (x : α) → β x` {br}[] ⊢ f = g
  + `funext x`
  + `f g : (x : α) → β x` {br}`x : α` {br}[] ⊢ f x = g x
:::

*Remarks:*

* `funext` is a special case of the more general `ext` tactic. Use
  `funext` when you specifically want to compare two functions
  pointwise; use `ext` when the goal involves more than one layer
  of extensionality (e.g. functions returning sets).
* You can introduce several variables at once, e.g. `funext x y` to
  reduce `(fun x y ↦ f x y) = (fun x y ↦ g x y)` to `f x y = g x y`.



::::keepEnv
:::example " "
```lean
example : (fun n : ℕ ↦ n + 0) = (fun n : ℕ ↦ n) := by
  funext n
  simp

example (f : ℕ → ℕ → ℕ) :
    (fun n m ↦ f n m) = f := by
  funext n m
  rfl
```

{docstring funext}

:::
::::
