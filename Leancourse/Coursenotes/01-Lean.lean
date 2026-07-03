import VersoManual

import «Leancourse».Coursenotes.«01-Lean».«01-Types»
import «Leancourse».Coursenotes.«01-Lean».«02-Functions»
import «Leancourse».Coursenotes.«01-Lean».«03-Typeclasses»
import «Leancourse».Coursenotes.«01-Lean».«04-CurryHoward»
import «Leancourse».Coursenotes.«01-Lean».«05-DependentTypes»
import «Leancourse».Coursenotes.«01-Lean».«06-Notation»

open Verso.Genre Manual

#doc (Manual) "Lean and its type theory" =>
%%%
htmlSplit := .never
tag := "lean"
%%%

This part covers Lean both as a practical proof assistant and as the
dependent type theory it is built on.  We begin with types and the
universe hierarchy -- including how to define your own types with
`inductive` and `structure` -- then functions and terms and the
typeclass system.  We then turn to the theory: the Curry-Howard
correspondence tying propositions to types and proofs to terms (and,
with it, how to prove things interactively), dependent types, and
finally notation.
(Several reference topics -- the alphabetical tactic glossary, how a
Lean file is organized, Lean's brackets, equality and reduction, the
diagnostic commands, and Navigating Mathlib -- live in the
{ref "appendix"}[Appendix]; the deeper foundations, the axioms of Lean
and well-foundedness, are treated in the *Mathematics* part.)

{include 0  «Leancourse».Coursenotes.«01-Lean».«01-Types»}

{include 0  «Leancourse».Coursenotes.«01-Lean».«02-Functions»}

{include 0  «Leancourse».Coursenotes.«01-Lean».«03-Typeclasses»}

{include 0  «Leancourse».Coursenotes.«01-Lean».«04-CurryHoward»}

{include 0  «Leancourse».Coursenotes.«01-Lean».«05-DependentTypes»}

{include 0  «Leancourse».Coursenotes.«01-Lean».«06-Notation»}
