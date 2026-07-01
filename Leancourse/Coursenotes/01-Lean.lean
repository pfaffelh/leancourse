import VersoManual

import «Leancourse».Coursenotes.«01-Lean».«01-Notes-Lean»
import «Leancourse».Coursenotes.«01-Lean».«02-Notes-Proofs»
import «Leancourse».Coursenotes.«01-Lean».«03-FunctionalBasics»
import «Leancourse».Coursenotes.«01-Lean».«Universes»
import «Leancourse».Coursenotes.«01-Lean».«03b-Functions»
import «Leancourse».Coursenotes.«01-Lean».«Inductive»
import «Leancourse».Coursenotes.«01-Lean».«04-NavigatingMathlib»
import «Leancourse».Coursenotes.«02-TypeTheory».«01-CurryHoward»
import «Leancourse».Coursenotes.«02-TypeTheory».«02-DependentTypes»
import «Leancourse».Coursenotes.«02-TypeTheory».«04-Structures»
import «Leancourse».Coursenotes.«02-TypeTheory».«05-Typeclasses»

open Verso.Genre Manual

#doc (Manual) "Lean and its type theory" =>
%%%
htmlSplit := .never
tag := "lean"
%%%

This part covers Lean both as a practical proof assistant and as the
dependent type theory it is built on.  The first chapters are
hands-on -- the language itself, writing proofs, functional
programming, and navigating Mathlib.  The later chapters turn to the
theory: the Curry-Howard correspondence, dependent types, and the
`structure` / `class` machinery that underpins Mathlib.  (The
alphabetical tactic glossary lives in the Appendix; the deeper
foundations -- universes, the axioms of Lean, and well-foundedness --
are treated in the *Mathematics* part.)

{include 0  «Leancourse».Coursenotes.«01-Lean».«03-FunctionalBasics»}

{include 0  «Leancourse».Coursenotes.«01-Lean».«Universes»}

{include 0  «Leancourse».Coursenotes.«01-Lean».«03b-Functions»}

{include 0  «Leancourse».Coursenotes.«01-Lean».«Inductive»}

{include 0  «Leancourse».Coursenotes.«01-Lean».«01-Notes-Lean»}

{include 0  «Leancourse».Coursenotes.«01-Lean».«02-Notes-Proofs»}

{include 0  «Leancourse».Coursenotes.«01-Lean».«04-NavigatingMathlib»}

{include 0  «Leancourse».Coursenotes.«02-TypeTheory».«01-CurryHoward»}

{include 0  «Leancourse».Coursenotes.«02-TypeTheory».«02-DependentTypes»}

{include 0  «Leancourse».Coursenotes.«02-TypeTheory».«04-Structures»}

{include 0  «Leancourse».Coursenotes.«02-TypeTheory».«05-Typeclasses»}
