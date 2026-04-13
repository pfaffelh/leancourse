import Lean
import VersoManual
import Manual.Meta
import Leancourse.Misc.Defs
import Mathlib
open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open MyDef

set_option pp.rawOnError true

#doc (Manual) "`push_cast`" =>
%%%
tag := "push-cast"
%%%

*Summary:* `push_cast` pushes coercions (like `Nat.cast`,
`Int.cast`, `Rat.cast`) *towards the leaves* of an expression. It
turns `((a + b : ℕ) : ℝ)` into `(a : ℝ) + (b : ℝ)`, and similarly
for `*`, `^`, etc. This is the inverse direction of `norm_cast`,
which moves casts outward.

*Examples:*

:::table (align := left) +header
* + Proof state
  + Tactic
  + New proof state
* + `n : ℕ` {br}[] ⊢ ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1
  + `push_cast`
  + `n : ℕ` {br}[] ⊢ (n : ℝ) + 1 = (n : ℝ) + 1
:::

*Remarks:*

* Use `push_cast` when the cast sits *outside* a compound
  expression and you want to distribute it; use `norm_cast` when
  the casts sit on atoms and you want to pull them out.
* The idiomatic combination for closing casting goals is
  `push_cast; ring` (or `push_cast; linarith`).
* `push_cast at h` rewrites a hypothesis.



::::keepEnv
:::example " "
```lean
example (n : ℕ) : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by
  push_cast
  ring

example (k : ℕ) : ((k ^ 2 : ℕ) : ℝ) = (k : ℝ) ^ 2 := by
  push_cast
  ring
```

:::
::::
