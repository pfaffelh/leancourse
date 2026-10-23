import VersoManual
import Manual.Meta
import Leancourse.Markup
import Mathlib

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open MyDef

set_option pp.rawOnError true

#doc (Manual) "`suffices`" =>
%%%
tag := "suffices"
%%%

*Summary:* `suffices h : P` says that `P` would be enough to finish. It leaves two goals: first close the original goal using `h : P`, then prove `P`.

*Examples*

:::table (align := left) +header
* + Proof state
  + Tactic
  + New proof state
* + `hPQ : P → Q` {br}[] ⊢ Q
  + `suffices h : P by exact hPQ h`
  + `hPQ : P → Q` {br}[] ⊢ P
* + `hPQ : P → Q` {br}[] ⊢ Q
  + `suffices h : P`
  + `h : P` {br}[] ⊢ Q {br}[] *and* ⊢ P
:::

*Notes*

`suffices` is {ref "have"}[`have`] read backwards. `have h : P := ...` proves `P` first and then uses it; `suffices h : P` uses `P` first and proves it afterwards.

Which one to pick is a question of how the proof reads. Use `have` when the intermediate fact is a step forward from what you know. Use `suffices` when it is a reduction of what you want — "it is enough to show ..." is exactly how such a step is phrased on paper.

The short form `suffices h : P by tac` closes the first goal with `tac` immediately and leaves only `⊢ P`.

{docstring Lean.Parser.Tactic.tacticSuffices_}
