import VersoManual

import «Leancourse».Coursenotes.«04-Appendix».«Tactics».«Cheatsheet»
import «Leancourse».Coursenotes.«04-Appendix».«Tactics».«Aesop»
import «Leancourse».Coursenotes.«04-Appendix».«Tactics».«Grind»
import «Leancourse».Coursenotes.«04-Appendix».«Tactics».«Linear_combination»
import «Leancourse».Coursenotes.«04-Appendix».«Tactics».«Polyrith»
import «Leancourse».Coursenotes.«04-Appendix».«Tactics».«Apply»
import «Leancourse».Coursenotes.«04-Appendix».«Tactics».«Applyqm»
import «Leancourse».Coursenotes.«04-Appendix».«Tactics».«Assumption»
import «Leancourse».Coursenotes.«04-Appendix».«Tactics».«By_cases»
import «Leancourse».Coursenotes.«04-Appendix».«Tactics».«By_contra»
import «Leancourse».Coursenotes.«04-Appendix».«Tactics».«Calc»
import «Leancourse».Coursenotes.«04-Appendix».«Tactics».«Cases»
import «Leancourse».Coursenotes.«04-Appendix».«Tactics».«Change»
import «Leancourse».Coursenotes.«04-Appendix».«Tactics».«Clear»
import «Leancourse».Coursenotes.«04-Appendix».«Tactics».«Congr»
import «Leancourse».Coursenotes.«04-Appendix».«Tactics».«Constructor»
import «Leancourse».Coursenotes.«04-Appendix».«Tactics».«Contradiction»
import «Leancourse».Coursenotes.«04-Appendix».«Tactics».«Contrapose»
import «Leancourse».Coursenotes.«04-Appendix».«Tactics».«Decide»
import «Leancourse».Coursenotes.«04-Appendix».«Tactics».«Exact»
import «Leancourse».Coursenotes.«04-Appendix».«Tactics».«Exfalso»
import «Leancourse».Coursenotes.«04-Appendix».«Tactics».«Ext»
import «Leancourse».Coursenotes.«04-Appendix».«Tactics».«Field_simp»
import «Leancourse».Coursenotes.«04-Appendix».«Tactics».«Filter_upwards»
import «Leancourse».Coursenotes.«04-Appendix».«Tactics».«Fun_prop»
import «Leancourse».Coursenotes.«04-Appendix».«Tactics».«Funext»
import «Leancourse».Coursenotes.«04-Appendix».«Tactics».«Gcongr»
import «Leancourse».Coursenotes.«04-Appendix».«Tactics».«Nlinarith»
import «Leancourse».Coursenotes.«04-Appendix».«Tactics».«Norm_cast»
import «Leancourse».Coursenotes.«04-Appendix».«Tactics».«Omega»
import «Leancourse».Coursenotes.«04-Appendix».«Tactics».«Positivity»
import «Leancourse».Coursenotes.«04-Appendix».«Tactics».«Push_cast»
import «Leancourse».Coursenotes.«04-Appendix».«Tactics».«Ring_nf»
import «Leancourse».Coursenotes.«04-Appendix».«Tactics».«Have»
import «Leancourse».Coursenotes.«04-Appendix».«Tactics».«Induction»
import «Leancourse».Coursenotes.«04-Appendix».«Tactics».«Intro»
import «Leancourse».Coursenotes.«04-Appendix».«Tactics».«Left»
import «Leancourse».Coursenotes.«04-Appendix».«Tactics».«Linarith»
import «Leancourse».Coursenotes.«04-Appendix».«Tactics».«Norm_num»
import «Leancourse».Coursenotes.«04-Appendix».«Tactics».«Nth_rewrite»
import «Leancourse».Coursenotes.«04-Appendix».«Tactics».«Obtain»
import «Leancourse».Coursenotes.«04-Appendix».«Tactics».«Push_neg»
import «Leancourse».Coursenotes.«04-Appendix».«Tactics».«Rcases»
import «Leancourse».Coursenotes.«04-Appendix».«Tactics».«Refine»
import «Leancourse».Coursenotes.«04-Appendix».«Tactics».«Revert»
import «Leancourse».Coursenotes.«04-Appendix».«Tactics».«Rfl»
import «Leancourse».Coursenotes.«04-Appendix».«Tactics».«Right»
import «Leancourse».Coursenotes.«04-Appendix».«Tactics».«Ring»
import «Leancourse».Coursenotes.«04-Appendix».«Tactics».«Rintro»
import «Leancourse».Coursenotes.«04-Appendix».«Tactics».«Rw»
import «Leancourse».Coursenotes.«04-Appendix».«Tactics».«Set»
import «Leancourse».Coursenotes.«04-Appendix».«Tactics».«Show»
import «Leancourse».Coursenotes.«04-Appendix».«Tactics».«Simp»
import «Leancourse».Coursenotes.«04-Appendix».«Tactics».«Simp_rw»
import «Leancourse».Coursenotes.«04-Appendix».«Tactics».«Specialize»
import «Leancourse».Coursenotes.«04-Appendix».«Tactics».«Symm»
import «Leancourse».Coursenotes.«04-Appendix».«Tactics».«Tauto»
import «Leancourse».Coursenotes.«04-Appendix».«Tactics».«Triv»
import «Leancourse».Coursenotes.«04-Appendix».«Tactics».«Trivial»
import «Leancourse».Coursenotes.«04-Appendix».«Tactics».«Use»

open Verso.Genre Manual

set_option pp.rawOnError true

#doc (Manual) "Tactics" =>
%%%
htmlSplit := .never
tag := "tactics"
%%%

This chapter is an *alphabetical glossary*: look up a tactic by name.

*The everyday core.* A handful of tactics do most of the work in most
proofs: {ref "exact"}[`exact`] (hand over the goal's proof term
directly), {ref "apply"}[`apply`] (reduce the goal to a lemma's
hypotheses), {ref "rw"}[`rw`] (rewrite with an equation or `↔`),
{ref "intro"}[`intro`] (move a hypothesis into context), and
{ref "simp"}[`simp`] (simplify with known lemmas).

*When you don't know what to use, ask.* The *search* tactics propose a
step for you -- reach for them constantly: {ref "exact"}[`exact?`]
looks for a library term that closes the goal, {ref "apply-qm"}[`apply?`]
for a lemma to `apply`, {ref "rw"}[`rw?`] for a rewrite that fits, and
{ref "simp"}[`simp?`] reports which simp lemmas fired (so you can then
switch to a robust `simp only [...]`).

Before the alphabetical list, here is a rough guide to which
*automation* tactic fits which kind of goal.

:::table +header
* + Goal type
  + Tactic
* + Numerical computation (`2 + 3 = 5`)
  + `norm_num` or `decide`
* + Linear arithmetic over `ℕ`, `ℤ`
  + `omega`
* + Linear arithmetic over `ℝ`, `ℚ`
  + `linarith`
* + Ring equality (`(x+y)^2 = ...`)
  + `ring`
* + Nonlinear inequality
  + `nlinarith` or `positivity`
* + Clearing denominators
  + `field_simp` then `ring`
* + Simplification with known lemmas
  + `simp` / `simp only [...]`
* + Mixed equality, arithmetic, case splits
  + `grind`
* + Set membership, basic logic
  + `aesop`
* + Monotonicity / congruence
  + `gcongr`
* + Equality from a combination of hypotheses
  + `linear_combination`
:::

When in doubt, try `simp`, then `grind` or `aesop`, then a more
specialized tactic. Use `simp?` to see which simp lemmas apply and
switch to `simp only` for a robust proof.

{include 0 «Leancourse».Coursenotes.«04-Appendix».«Tactics».«Cheatsheet»}

{include 0 «Leancourse».Coursenotes.«04-Appendix».«Tactics».«Aesop»}

{include 0 «Leancourse».Coursenotes.«04-Appendix».«Tactics».«Apply»}

{include 0 «Leancourse».Coursenotes.«04-Appendix».«Tactics».«Applyqm»}

{include 0 «Leancourse».Coursenotes.«04-Appendix».«Tactics».«Assumption»}

{include 0 «Leancourse».Coursenotes.«04-Appendix».«Tactics».«By_cases»}

{include 0 «Leancourse».Coursenotes.«04-Appendix».«Tactics».«By_contra»}

{include 0  «Leancourse».Coursenotes.«04-Appendix».«Tactics».«Calc»}

{include 0  «Leancourse».Coursenotes.«04-Appendix».«Tactics».«Cases»}

{include 0  «Leancourse».Coursenotes.«04-Appendix».«Tactics».«Change»}

{include 0  «Leancourse».Coursenotes.«04-Appendix».«Tactics».«Clear»}

{include 0  «Leancourse».Coursenotes.«04-Appendix».«Tactics».«Congr»}

{include 0  «Leancourse».Coursenotes.«04-Appendix».«Tactics».«Constructor»}

{include 0  «Leancourse».Coursenotes.«04-Appendix».«Tactics».«Contradiction»}

{include 0  «Leancourse».Coursenotes.«04-Appendix».«Tactics».«Contrapose»}

{include 0  «Leancourse».Coursenotes.«04-Appendix».«Tactics».«Decide»}

{include 0  «Leancourse».Coursenotes.«04-Appendix».«Tactics».«Exact»}

{include 0  «Leancourse».Coursenotes.«04-Appendix».«Tactics».«Exfalso»}

{include 0  «Leancourse».Coursenotes.«04-Appendix».«Tactics».«Ext»}

{include 0  «Leancourse».Coursenotes.«04-Appendix».«Tactics».«Funext»}

{include 0  «Leancourse».Coursenotes.«04-Appendix».«Tactics».«Field_simp»}

{include 0  «Leancourse».Coursenotes.«04-Appendix».«Tactics».«Filter_upwards»}

{include 0  «Leancourse».Coursenotes.«04-Appendix».«Tactics».«Fun_prop»}

{include 0  «Leancourse».Coursenotes.«04-Appendix».«Tactics».«Gcongr»}

{include 0  «Leancourse».Coursenotes.«04-Appendix».«Tactics».«Grind»}

{include 0  «Leancourse».Coursenotes.«04-Appendix».«Tactics».«Nlinarith»}

{include 0  «Leancourse».Coursenotes.«04-Appendix».«Tactics».«Norm_cast»}

{include 0  «Leancourse».Coursenotes.«04-Appendix».«Tactics».«Omega»}

{include 0  «Leancourse».Coursenotes.«04-Appendix».«Tactics».«Polyrith»}

{include 0  «Leancourse».Coursenotes.«04-Appendix».«Tactics».«Positivity»}

{include 0  «Leancourse».Coursenotes.«04-Appendix».«Tactics».«Push_cast»}

{include 0  «Leancourse».Coursenotes.«04-Appendix».«Tactics».«Ring_nf»}

{include 0  «Leancourse».Coursenotes.«04-Appendix».«Tactics».«Have»}

{include 0  «Leancourse».Coursenotes.«04-Appendix».«Tactics».«Induction»}

{include 0  «Leancourse».Coursenotes.«04-Appendix».«Tactics».«Intro»}

{include 0  «Leancourse».Coursenotes.«04-Appendix».«Tactics».«Left»}

{include 0  «Leancourse».Coursenotes.«04-Appendix».«Tactics».«Linarith»}

{include 0  «Leancourse».Coursenotes.«04-Appendix».«Tactics».«Linear_combination»}

{include 0  «Leancourse».Coursenotes.«04-Appendix».«Tactics».«Norm_num»}

{include 0  «Leancourse».Coursenotes.«04-Appendix».«Tactics».«Nth_rewrite»}

{include 0  «Leancourse».Coursenotes.«04-Appendix».«Tactics».«Obtain»}

{include 0  «Leancourse».Coursenotes.«04-Appendix».«Tactics».«Push_neg»}

{include 0  «Leancourse».Coursenotes.«04-Appendix».«Tactics».«Rcases»}

{include 0  «Leancourse».Coursenotes.«04-Appendix».«Tactics».«Refine»}

{include 0  «Leancourse».Coursenotes.«04-Appendix».«Tactics».«Revert»}

{include 0  «Leancourse».Coursenotes.«04-Appendix».«Tactics».«Rfl»}

{include 0  «Leancourse».Coursenotes.«04-Appendix».«Tactics».«Right»}

{include 0  «Leancourse».Coursenotes.«04-Appendix».«Tactics».«Ring»}

{include 0  «Leancourse».Coursenotes.«04-Appendix».«Tactics».«Rintro»}

{include 0  «Leancourse».Coursenotes.«04-Appendix».«Tactics».«Rw»}

{include 0  «Leancourse».Coursenotes.«04-Appendix».«Tactics».«Set»}

{include 0  «Leancourse».Coursenotes.«04-Appendix».«Tactics».«Show»}

{include 0  «Leancourse».Coursenotes.«04-Appendix».«Tactics».«Simp»}

{include 0  «Leancourse».Coursenotes.«04-Appendix».«Tactics».«Simp_rw»}

{include 0  «Leancourse».Coursenotes.«04-Appendix».«Tactics».«Specialize»}

{include 0  «Leancourse».Coursenotes.«04-Appendix».«Tactics».«Symm»}

{include 0  «Leancourse».Coursenotes.«04-Appendix».«Tactics».«Tauto»}

{include 0  «Leancourse».Coursenotes.«04-Appendix».«Tactics».«Triv»}

{include 0  «Leancourse».Coursenotes.«04-Appendix».«Tactics».«Trivial»}

{include 0  «Leancourse».Coursenotes.«04-Appendix».«Tactics».«Use»}
