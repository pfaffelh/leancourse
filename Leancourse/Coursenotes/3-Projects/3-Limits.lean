import VersoManual
import Manual.Meta
import Leancourse.Coursenotes.References

open Verso.Genre Manual
open Leancourse.Refs

#doc (Manual) "Project 3: Limits of sequences, with and without filters" =>
%%%
tag := "project-limits"
%%%

*What it is.*  In the {ref "filters"}[filters chapter] we saw that
Mathlib phrases convergence via `Filter.Tendsto`.  This project
builds the classical theory first — the epsilon-N definition from
Analysis 1 — and then proves that the two formulations agree.  It is
the ideal project if you want to formalize material you know very
well and see the filter language pay off.

*Implementation idea.*  Define
`TendsTo (a : ℕ → ℝ) (t : ℝ) : Prop` by the usual quantifier chain
(for every positive epsilon there is an N beyond which the distance
is below epsilon).  Then build the toolbox: limits are unique; a
constant sequence converges; limits respect sums, scalar multiples,
and products; the squeeze theorem.  Expect to practice `intro`,
`obtain`, `specialize`, and the art of choosing the right `N` (a
`max` of two thresholds) — plus `linarith` and `abs` lemmas.
Finally, prove the bridge:
`TendsTo a t ↔ Filter.Tendsto a Filter.atTop (nhds t)`, using
Mathlib's `Metric.tendsto_atTop` as the stepping stone, and reprove
one of your toolbox lemmas in one line with
{ref "filter-tendsto"}[the filter API].  Stretch goal: monotone
bounded sequences converge (this needs the completeness of `ℝ` via
suprema).

*References.*  {citet mathematicsInLean}[] develops exactly this
programme in its convergence chapter, and {citet buzzardMehta}[]
cover limits of sequences as a running example; consult them when
stuck, not before.
