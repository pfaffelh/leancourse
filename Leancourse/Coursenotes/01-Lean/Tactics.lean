import VersoManual

import «Leancourse».Coursenotes.«01-Lean».«Tactics».«Cheatsheet»
import «Leancourse».Coursenotes.«01-Lean».«Tactics».«Apply»
import «Leancourse».Coursenotes.«01-Lean».«Tactics».«Applyqm»
import «Leancourse».Coursenotes.«01-Lean».«Tactics».«Assumption»
import «Leancourse».Coursenotes.«01-Lean».«Tactics».«By_cases»
import «Leancourse».Coursenotes.«01-Lean».«Tactics».«By_contra»
import «Leancourse».Coursenotes.«01-Lean».«Tactics».«Calc»
import «Leancourse».Coursenotes.«01-Lean».«Tactics».«Cases»
import «Leancourse».Coursenotes.«01-Lean».«Tactics».«Change»
import «Leancourse».Coursenotes.«01-Lean».«Tactics».«Clear»
import «Leancourse».Coursenotes.«01-Lean».«Tactics».«Congr»
import «Leancourse».Coursenotes.«01-Lean».«Tactics».«Constructor»
import «Leancourse».Coursenotes.«01-Lean».«Tactics».«Contradiction»
import «Leancourse».Coursenotes.«01-Lean».«Tactics».«Contrapose»
import «Leancourse».Coursenotes.«01-Lean».«Tactics».«Decide»
import «Leancourse».Coursenotes.«01-Lean».«Tactics».«Exact»
import «Leancourse».Coursenotes.«01-Lean».«Tactics».«Exfalso»
import «Leancourse».Coursenotes.«01-Lean».«Tactics».«Ext»
import «Leancourse».Coursenotes.«01-Lean».«Tactics».«Field_simp»
import «Leancourse».Coursenotes.«01-Lean».«Tactics».«Filter_upwards»
import «Leancourse».Coursenotes.«01-Lean».«Tactics».«Fun_prop»
import «Leancourse».Coursenotes.«01-Lean».«Tactics».«Funext»
import «Leancourse».Coursenotes.«01-Lean».«Tactics».«Gcongr»
import «Leancourse».Coursenotes.«01-Lean».«Tactics».«Nlinarith»
import «Leancourse».Coursenotes.«01-Lean».«Tactics».«Norm_cast»
import «Leancourse».Coursenotes.«01-Lean».«Tactics».«Omega»
import «Leancourse».Coursenotes.«01-Lean».«Tactics».«Positivity»
import «Leancourse».Coursenotes.«01-Lean».«Tactics».«Push_cast»
import «Leancourse».Coursenotes.«01-Lean».«Tactics».«Ring_nf»
import «Leancourse».Coursenotes.«01-Lean».«Tactics».«Have»
import «Leancourse».Coursenotes.«01-Lean».«Tactics».«Induction»
import «Leancourse».Coursenotes.«01-Lean».«Tactics».«Intro»
import «Leancourse».Coursenotes.«01-Lean».«Tactics».«Left»
import «Leancourse».Coursenotes.«01-Lean».«Tactics».«Linarith»
import «Leancourse».Coursenotes.«01-Lean».«Tactics».«Norm_num»
import «Leancourse».Coursenotes.«01-Lean».«Tactics».«Nth_rewrite»
import «Leancourse».Coursenotes.«01-Lean».«Tactics».«Obtain»
import «Leancourse».Coursenotes.«01-Lean».«Tactics».«Push_neg»
import «Leancourse».Coursenotes.«01-Lean».«Tactics».«Rcases»
import «Leancourse».Coursenotes.«01-Lean».«Tactics».«Refine»
import «Leancourse».Coursenotes.«01-Lean».«Tactics».«Revert»
import «Leancourse».Coursenotes.«01-Lean».«Tactics».«Rfl»
import «Leancourse».Coursenotes.«01-Lean».«Tactics».«Right»
import «Leancourse».Coursenotes.«01-Lean».«Tactics».«Ring»
import «Leancourse».Coursenotes.«01-Lean».«Tactics».«Rintro»
import «Leancourse».Coursenotes.«01-Lean».«Tactics».«Rw»
import «Leancourse».Coursenotes.«01-Lean».«Tactics».«Set»
import «Leancourse».Coursenotes.«01-Lean».«Tactics».«Show»
import «Leancourse».Coursenotes.«01-Lean».«Tactics».«Simp»
import «Leancourse».Coursenotes.«01-Lean».«Tactics».«Simp_rw»
import «Leancourse».Coursenotes.«01-Lean».«Tactics».«Specialize»
import «Leancourse».Coursenotes.«01-Lean».«Tactics».«Symm»
import «Leancourse».Coursenotes.«01-Lean».«Tactics».«Tauto»
import «Leancourse».Coursenotes.«01-Lean».«Tactics».«Triv»
import «Leancourse».Coursenotes.«01-Lean».«Tactics».«Trivial»
import «Leancourse».Coursenotes.«01-Lean».«Tactics».«Use»

open Verso.Genre Manual

set_option pp.rawOnError true

#doc (Manual) "Tactics" =>
%%%
htmlSplit := .never
tag := "tactics"
%%%

{include 0 «Leancourse».Coursenotes.«01-Lean».«Tactics».«Cheatsheet»}

{include 0 «Leancourse».Coursenotes.«01-Lean».«Tactics».«Apply»}

{include 0 «Leancourse».Coursenotes.«01-Lean».«Tactics».«Applyqm»}

{include 0 «Leancourse».Coursenotes.«01-Lean».«Tactics».«Assumption»}

{include 0 «Leancourse».Coursenotes.«01-Lean».«Tactics».«By_cases»}

{include 0 «Leancourse».Coursenotes.«01-Lean».«Tactics».«By_contra»}

{include 0  «Leancourse».Coursenotes.«01-Lean».«Tactics».«Calc»}

{include 0  «Leancourse».Coursenotes.«01-Lean».«Tactics».«Cases»}

{include 0  «Leancourse».Coursenotes.«01-Lean».«Tactics».«Change»}

{include 0  «Leancourse».Coursenotes.«01-Lean».«Tactics».«Clear»}

{include 0  «Leancourse».Coursenotes.«01-Lean».«Tactics».«Congr»}

{include 0  «Leancourse».Coursenotes.«01-Lean».«Tactics».«Constructor»}

{include 0  «Leancourse».Coursenotes.«01-Lean».«Tactics».«Contradiction»}

{include 0  «Leancourse».Coursenotes.«01-Lean».«Tactics».«Contrapose»}

{include 0  «Leancourse».Coursenotes.«01-Lean».«Tactics».«Decide»}

{include 0  «Leancourse».Coursenotes.«01-Lean».«Tactics».«Exact»}

{include 0  «Leancourse».Coursenotes.«01-Lean».«Tactics».«Exfalso»}

{include 0  «Leancourse».Coursenotes.«01-Lean».«Tactics».«Ext»}

{include 0  «Leancourse».Coursenotes.«01-Lean».«Tactics».«Funext»}

{include 0  «Leancourse».Coursenotes.«01-Lean».«Tactics».«Field_simp»}

{include 0  «Leancourse».Coursenotes.«01-Lean».«Tactics».«Filter_upwards»}

{include 0  «Leancourse».Coursenotes.«01-Lean».«Tactics».«Fun_prop»}

{include 0  «Leancourse».Coursenotes.«01-Lean».«Tactics».«Gcongr»}

{include 0  «Leancourse».Coursenotes.«01-Lean».«Tactics».«Nlinarith»}

{include 0  «Leancourse».Coursenotes.«01-Lean».«Tactics».«Norm_cast»}

{include 0  «Leancourse».Coursenotes.«01-Lean».«Tactics».«Omega»}

{include 0  «Leancourse».Coursenotes.«01-Lean».«Tactics».«Positivity»}

{include 0  «Leancourse».Coursenotes.«01-Lean».«Tactics».«Push_cast»}

{include 0  «Leancourse».Coursenotes.«01-Lean».«Tactics».«Ring_nf»}

{include 0  «Leancourse».Coursenotes.«01-Lean».«Tactics».«Have»}

{include 0  «Leancourse».Coursenotes.«01-Lean».«Tactics».«Induction»}

{include 0  «Leancourse».Coursenotes.«01-Lean».«Tactics».«Intro»}

{include 0  «Leancourse».Coursenotes.«01-Lean».«Tactics».«Left»}

{include 0  «Leancourse».Coursenotes.«01-Lean».«Tactics».«Linarith»}

{include 0  «Leancourse».Coursenotes.«01-Lean».«Tactics».«Norm_num»}

{include 0  «Leancourse».Coursenotes.«01-Lean».«Tactics».«Nth_rewrite»}

{include 0  «Leancourse».Coursenotes.«01-Lean».«Tactics».«Obtain»}

{include 0  «Leancourse».Coursenotes.«01-Lean».«Tactics».«Push_neg»}

{include 0  «Leancourse».Coursenotes.«01-Lean».«Tactics».«Rcases»}

{include 0  «Leancourse».Coursenotes.«01-Lean».«Tactics».«Refine»}

{include 0  «Leancourse».Coursenotes.«01-Lean».«Tactics».«Revert»}

{include 0  «Leancourse».Coursenotes.«01-Lean».«Tactics».«Rfl»}

{include 0  «Leancourse».Coursenotes.«01-Lean».«Tactics».«Right»}

{include 0  «Leancourse».Coursenotes.«01-Lean».«Tactics».«Ring»}

{include 0  «Leancourse».Coursenotes.«01-Lean».«Tactics».«Rintro»}

{include 0  «Leancourse».Coursenotes.«01-Lean».«Tactics».«Rw»}

{include 0  «Leancourse».Coursenotes.«01-Lean».«Tactics».«Set»}

{include 0  «Leancourse».Coursenotes.«01-Lean».«Tactics».«Show»}

{include 0  «Leancourse».Coursenotes.«01-Lean».«Tactics».«Simp»}

{include 0  «Leancourse».Coursenotes.«01-Lean».«Tactics».«Simp_rw»}

{include 0  «Leancourse».Coursenotes.«01-Lean».«Tactics».«Specialize»}

{include 0  «Leancourse».Coursenotes.«01-Lean».«Tactics».«Symm»}

{include 0  «Leancourse».Coursenotes.«01-Lean».«Tactics».«Tauto»}

{include 0  «Leancourse».Coursenotes.«01-Lean».«Tactics».«Triv»}

{include 0  «Leancourse».Coursenotes.«01-Lean».«Tactics».«Trivial»}

{include 0  «Leancourse».Coursenotes.«01-Lean».«Tactics».«Use»}
