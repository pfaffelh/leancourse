import Lean
import VersoManual
import Manual.Meta
import Leancourse.Misc.Defs
import Mathlib

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open MyDef

set_option pp.rawOnError true

#doc (Manual) "`let`, `letI`, `haveI`" =>
%%%
tag := "let"
%%%

*Summary:* `let` and {ref "have"}[`have`] both introduce a local hypothesis, but they differ in what they *remember*. `let x := e` keeps the *value*: `x` is *definitionally equal* to `e`, so later steps may unfold `x` back to `e`. `have h : P := e` keeps only the *type* `P` and forgets the term `e`, which becomes opaque. For proofs this is exactly right -- by {ref "types"}[proof irrelevance] the particular term does not matter -- so use `have` for `Prop`s and `let` for *data* you will compute with.

The `I`-suffixed variants `haveI` and `letI` do the same for *instances*: they add the given term to the local *instance cache*, so that typeclass resolution can find it. `haveI` adds it opaquely, `letI` transparently (keeping the definitional value). Reach for them when you must supply a typeclass instance by hand in the middle of a proof.

*Examples:*

::::keepEnv
:::example "`let` keeps the value; `have` forgets it"
```lean
example : (4 : ℕ) = 2 + 2 := by
  let x := 2
  -- x : ℕ := 2   (value kept: x unfolds to 2)
  show (4 : ℕ) = x + x
  rfl

example : True := by
  have y : ℕ := 2
  -- y : ℕ        (only the type remains)
  trivial
```
:::
::::

::::keepEnv
:::example "`haveI`: supplying an instance locally"
```lean
example : True := by
  haveI : Inhabited ℕ := ⟨0⟩   -- now `Inhabited ℕ` is in scope
  trivial
```
:::
::::

*Notes*

* The same keywords exist in *term* mode: `let x := e; body` and `have h : P := e; body`. The tactics are their proof-mode counterparts.
* `set x := e with hx` (see {ref "set-tactic"}[`set`]) is like `let`, but it *also* replaces `e` by `x` everywhere in the goal and records `hx : x = e`.
