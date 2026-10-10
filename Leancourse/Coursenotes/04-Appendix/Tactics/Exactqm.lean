import VersoManual
import Manual.Meta
import Leancourse.Misc.Defs
import Mathlib

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open Lean.MessageSeverity
open MyDef

set_option pp.rawOnError true

#doc (Manual) "`exact?`" =>
%%%
tag := "exact-qm"
%%%

*Summary:* `exact?` searches `Mathlib` for a single lemma that closes the goal outright. If it finds one, it reports it; clicking the suggestion inserts it in place of the `exact?`.

*Examples*

:::table (align := left) +header
* + Proof state
  + Tactic
  + New proof state
* + ⊢ ¬¬P ↔ P
  + `exact?`
  + *no goals* {br}[] Try this: `exact not_not`
* + ⊢ P ∧ Q ↔ Q ∧ P
  + `exact?`
  + *no goals* {br}[] Try this: `exact and_comm`
:::

*Notes*

The difference to {ref "apply-qm"}[`apply?`] is how much is left over. `exact?` wants a lemma that finishes the goal; `apply?` also accepts one that leaves new goals behind.

Both are slow, and both are search tools, not proof tools. Do not leave a call in a finished file: paste the result in its place. A file full of `exact?` takes minutes to compile and breaks when the library is reorganised.

Use it when you suspect the statement is already in `Mathlib`. For goals that are pure propositional logic, {ref "tauto"}[`tauto`] is faster and more reliable.

{docstring Lean.Parser.Tactic.exact?}
