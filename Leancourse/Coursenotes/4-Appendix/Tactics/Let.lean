import Lean
import VersoManual
import Manual.Meta
import Leancourse.Markup
import Mathlib

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open MyDef

set_option pp.rawOnError true

#doc (Manual) "`let`, `letI`, `haveI`" =>
%%%
tag := "let"
%%%

*Summary:* `let` and {ref "have"}[`have`] both introduce a local hypothesis, but they differ in what they *remember*. `let x := e` keeps the *value*: `x` is *definitionally equal* to `e`, so later steps may unfold `x` back to `e`. `have h : P := e` keeps only the *type* `P` and forgets the term `e`, which becomes opaque. For proofs this is exactly right — by {ref "types"}[proof irrelevance] the particular term does not matter — so use `have` for `Prop`s and `let` for *data* you will compute with.

A `have` or `let` whose type is a class also adds a local instance, which instance search uses for the rest of the proof. For a Prop class such as `Fact`, `have` suffices; for a data class whose value must compute (`decide`, `rfl`), use `let` (chapter 1.6, {ref "local-instances"}[Local instances]).

The `I`-suffixed variants `haveI` and `letI` behave like `have` and `let` while the proof is written. In the finished term they substitute the value instead of leaving a `have` or `let` binding. This matters for definitions and instances, not for proofs; in proofs Mathlib's linter `linter.style.haveILetI` asks for `have` and `let`.

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
:::example "A local instance: `let` keeps it computable"
```lean
def IsTiny (n : ℕ) : Prop := n < 3

-- with `have`, `decide` gets stuck at `this 2`
example : IsTiny 2 := by
  let _ : DecidablePred IsTiny :=
    fun n => inferInstanceAs (Decidable (n < 3))
  decide
```
:::
::::

*Notes*

* The same keywords exist in *term* mode: `let x := e; body` and `have h : P := e; body`. The tactics are their proof-mode counterparts.
* `set x := e with hx` (see {ref "set-tactic"}[`set`]) is like `let`, but it *also* replaces `e` by `x` everywhere in the goal and records `hx : x = e`.
