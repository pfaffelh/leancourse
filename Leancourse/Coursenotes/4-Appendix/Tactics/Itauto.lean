import VersoManual
import Manual.Meta
import Leancourse.Markup
import Mathlib

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open MyDef

set_option pp.rawOnError true

#doc (Manual) "`itauto`" =>
%%%
tag := "itauto"
%%%

*Summary:* `itauto` proves goals of propositional logic, like {ref "tauto"}[`tauto`], but reasons *intuitionistically*: it never uses the law of the excluded middle `P ∨ ¬P`.

*Examples*

:::table (align := left) +header
* + Proof state
  + Tactic
  + New proof state
* + ⊢ P ∧ Q → P
  + `itauto`
  + *No goals*
* + ⊢ P → ¬¬P
  + `itauto`
  + *No goals*
* + ⊢ ¬(P ∨ Q) ↔ ¬P ∧ ¬Q
  + `itauto`
  + *No goals*
* + ⊢ ¬¬P → P
  + `itauto`
  + *fails:* `itauto failed`
* + ⊢ ¬(P ∧ Q) ↔ ¬P ∨ ¬Q
  + `itauto`
  + *fails:* `itauto failed`
:::

*Notes*

The point of `itauto` is not that it is stronger than `tauto` — it is strictly weaker. The point is what its failure tells you.

A statement that `tauto` proves and `itauto` does not is a statement that *needs* the excluded middle. So the pair decides the question "is this classical?". Inspection does not: both De Morgan laws have the same shape, and only one of them is constructive.

This is worth trying on any goal where you wonder whether a proof has to go through {ref "by_cases"}[`by_cases`] or {ref "by_contra"}[`by_contra`]. If `itauto` closes the goal, a direct proof exists and the case split was avoidable.

`itauto` can be given a list of propositions to case on, as in `itauto [P, Q]`. It then uses the excluded middle for exactly those, and nothing else. That is a way to find the *smallest* classical assumption a proof needs.

The docstring below is `Mathlib`'s own and still mentions `tauto!`. That tactic no longer exists; read it as {ref "tauto"}[`tauto`], which is classical. `itauto!` does exist: it case-splits on every atom.

{docstring Mathlib.Tactic.ITauto.itauto}
