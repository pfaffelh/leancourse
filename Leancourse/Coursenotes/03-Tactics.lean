import Lean
import VersoManual
import DemoTextbook
import UsersGuide.Markup
import Leancourse.Meta.Table
import Leancourse.Misc.Defs

import «Leancourse».Coursenotes.«03-Tactics».«Cheatsheet»
import «Leancourse».Coursenotes.«03-Tactics».«Apply»
import «Leancourse».Coursenotes.«03-Tactics».«Apply?»
import «Leancourse».Coursenotes.«03-Tactics».«By_cases»
import «Leancourse».Coursenotes.«03-Tactics».«By_contra»
import «Leancourse».Coursenotes.«03-Tactics».«Calc»
import «Leancourse».Coursenotes.«03-Tactics».«Cases»
import «Leancourse».Coursenotes.«03-Tactics».«Change»
import «Leancourse».Coursenotes.«03-Tactics».«Clear»
import «Leancourse».Coursenotes.«03-Tactics».«Congr»
import «Leancourse».Coursenotes.«03-Tactics».«Constructor»
import «Leancourse».Coursenotes.«03-Tactics».«Exact»
import «Leancourse».Coursenotes.«03-Tactics».«Exfalso»
import «Leancourse».Coursenotes.«03-Tactics».«Have»
import «Leancourse».Coursenotes.«03-Tactics».«Induction»
import «Leancourse».Coursenotes.«03-Tactics».«Intro»
import «Leancourse».Coursenotes.«03-Tactics».«Left»
import «Leancourse».Coursenotes.«03-Tactics».«Linarith»
import «Leancourse».Coursenotes.«03-Tactics».«Nth_rewrite»
import «Leancourse».Coursenotes.«03-Tactics».«Obtain»
import «Leancourse».Coursenotes.«03-Tactics».«Push_neg»
import «Leancourse».Coursenotes.«03-Tactics».«Rcases»
import «Leancourse».Coursenotes.«03-Tactics».«Refine»
import «Leancourse».Coursenotes.«03-Tactics».«Revert»
import «Leancourse».Coursenotes.«03-Tactics».«Rfl»
import «Leancourse».Coursenotes.«03-Tactics».«Right»
import «Leancourse».Coursenotes.«03-Tactics».«Ring»
import «Leancourse».Coursenotes.«03-Tactics».«Rintro»
import «Leancourse».Coursenotes.«03-Tactics».«Rw»
import «Leancourse».Coursenotes.«03-Tactics».«Simp»
import «Leancourse».Coursenotes.«03-Tactics».«Specialize»
import «Leancourse».Coursenotes.«03-Tactics».«Tauto»
import «Leancourse».Coursenotes.«03-Tactics».«Triv»
import «Leancourse».Coursenotes.«03-Tactics».«Use»

open Verso.Genre Manual
open DemoTextbook.Exts

set_option pp.rawOnError true

#doc (Manual) "Tactics" =>
%%%
htmlSplit := .never
tag := "tactics"
%%%

{include 0 «Leancourse».Coursenotes.«03-Tactics».«Cheatsheet»}

{include 0 «Leancourse».Coursenotes.«03-Tactics».«Apply»}

{include 0 «Leancourse».Coursenotes.«03-Tactics».«Apply?»}

{include 0 «Leancourse».Coursenotes.«03-Tactics».«By_cases»}

{include 0 «Leancourse».Coursenotes.«03-Tactics».«By_contra»}

{include 0  «Leancourse».Coursenotes.«03-Tactics».«Calc»}

{include 0  «Leancourse».Coursenotes.«03-Tactics».«Cases»}

{include 0  «Leancourse».Coursenotes.«03-Tactics».«Change»}

{include 0  «Leancourse».Coursenotes.«03-Tactics».«Clear»}

{include 0  «Leancourse».Coursenotes.«03-Tactics».«Congr»}

{include 0  «Leancourse».Coursenotes.«03-Tactics».«Constructor»}

{include 0  «Leancourse».Coursenotes.«03-Tactics».«Exact»}

{include 0  «Leancourse».Coursenotes.«03-Tactics».«Exfalso»}

{include 0  «Leancourse».Coursenotes.«03-Tactics».«Have»}

{include 0  «Leancourse».Coursenotes.«03-Tactics».«Induction»}

{include 0  «Leancourse».Coursenotes.«03-Tactics».«Intro»}

{include 0  «Leancourse».Coursenotes.«03-Tactics».«Left»}

{include 0  «Leancourse».Coursenotes.«03-Tactics».«Linarith»}

{include 0  «Leancourse».Coursenotes.«03-Tactics».«Nth_rewrite»}

{include 0  «Leancourse».Coursenotes.«03-Tactics».«Obtain»}

{include 0  «Leancourse».Coursenotes.«03-Tactics».«Push_neg»}

{include 0  «Leancourse».Coursenotes.«03-Tactics».«Rcases»}

{include 0  «Leancourse».Coursenotes.«03-Tactics».«Refine»}

{include 0  «Leancourse».Coursenotes.«03-Tactics».«Revert»}

{include 0  «Leancourse».Coursenotes.«03-Tactics».«Rfl»}

{include 0  «Leancourse».Coursenotes.«03-Tactics».«Right»}

{include 0  «Leancourse».Coursenotes.«03-Tactics».«Ring»}

{include 0  «Leancourse».Coursenotes.«03-Tactics».«Rintro»}

{include 0  «Leancourse».Coursenotes.«03-Tactics».«Rw»}

{include 0  «Leancourse».Coursenotes.«03-Tactics».«Simp»}

{include 0  «Leancourse».Coursenotes.«03-Tactics».«Specialize»}

{include 0  «Leancourse».Coursenotes.«03-Tactics».«Tauto»}

{include 0  «Leancourse».Coursenotes.«03-Tactics».«Triv»}

{include 0  «Leancourse».Coursenotes.«03-Tactics».«Use»}
