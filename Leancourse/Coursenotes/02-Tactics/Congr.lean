import VersoManual
import Manual.Meta
import Leancourse.Misc.Defs
import Mathlib

open Lean.MessageSeverity
open Verso.Genre Manual
open MyDef

set_option pp.rawOnError true

#doc (Manual) "`congr`" =>
%%%
tag := "congr"
%%%

**Summary:** If you have to show an equality `f x = f y`, then `congr` uses the statement that the equality is particularly true if `x = y`.

**Examples:**

:::table (align := left) (header := true)
* + Proof state
  + Tactic
  + New proof state
* + `⊢ f x = f y`
  + `congr`
  + `⊢ x = y`
:::

**Remarks:**

* The related tactic `congr'` uses another parameter that determines how many recursive layers are eliminated in the goal; see the examples below.
* Besides the `congr` tactic there are several related results which can be applied, e.g. `tsum_congr`.


::::keepEnv
:::example " "
Here, `congr` goes too deep since it tries to match inner arguments:
```lean
example (f : ℝ → ℝ) (x y : ℝ) : f (x + y) = f (y + x) := by
  congr
  · sorry
  · sorry
```
We can prevent this by specifying how deep `congr` shoud go. (The above example is equivalent to `congr' 2`)
```lean
example (f : ℝ → ℝ) (x y : ℝ) : f (x + y) = f (y + x) := by
  congr 1
  exact add_comm x y
```
`tsum_congr` can be made usefule by using `apply` or a related tactics.
```lean (name := output) (error := false)
#print tsum_congr
```

```leanOutput output (severity := information)
theorem tsum_congr.{u_1, u_2} : ∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α] [inst_1 : TopologicalSpace α]
  {f g : β → α}, (∀ (b : β), f b = g b) → ∑' (b : β), f b = ∑' (b : β), g b :=
fun {α} {β} [AddCommMonoid α] [TopologicalSpace α] {f g} hfg => congr_arg tsum (funext hfg)
```

:::
::::
