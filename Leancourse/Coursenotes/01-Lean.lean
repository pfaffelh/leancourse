import VersoManual

import «Leancourse».Coursenotes.«01-Lean».«01-Universes»
import «Leancourse».Coursenotes.«01-Lean».«02-Functions»
import «Leancourse».Coursenotes.«01-Lean».«03-Inductive»
import «Leancourse».Coursenotes.«01-Lean».«04-Structures»
import «Leancourse».Coursenotes.«01-Lean».«05-Typeclasses»
import «Leancourse».Coursenotes.«01-Lean».«06-Parentheses»
import «Leancourse».Coursenotes.«01-Lean».«07-CurryHoward»
import «Leancourse».Coursenotes.«01-Lean».«08-DependentTypes»
import «Leancourse».Coursenotes.«01-Lean».«09-Equality»
import «Leancourse».Coursenotes.«01-Lean».«10-Proving»
import «Leancourse».Coursenotes.«01-Lean».«11-Exploring»
import «Leancourse».Coursenotes.«01-Lean».«12-Notation»

open Verso.Genre Manual

#doc (Manual) "Lean and its type theory" =>
%%%
htmlSplit := .never
tag := "lean"
%%%

This part covers Lean both as a practical proof assistant and as the
dependent type theory it is built on.  We begin with universes, types
and terms, then turn hands-on -- defining functions, inductive types,
structures and typeclasses -- and then to the theory (Curry-Howard,
dependent types, equality) and to proving propositions interactively.
The final chapters cover exploration and notation.
(The {ref "tactics"}[alphabetical tactic glossary] and
{ref "navigating-mathlib"}[Navigating Mathlib] live in the Appendix;
the deeper foundations -- the axioms of Lean and well-foundedness --
are treated in the *Mathematics* part.)

{include 0  «Leancourse».Coursenotes.«01-Lean».«01-Universes»}

{include 0  «Leancourse».Coursenotes.«01-Lean».«02-Functions»}

{include 0  «Leancourse».Coursenotes.«01-Lean».«03-Inductive»}

{include 0  «Leancourse».Coursenotes.«01-Lean».«04-Structures»}

{include 0  «Leancourse».Coursenotes.«01-Lean».«05-Typeclasses»}

{include 0  «Leancourse».Coursenotes.«01-Lean».«06-Parentheses»}

{include 0  «Leancourse».Coursenotes.«01-Lean».«07-CurryHoward»}

{include 0  «Leancourse».Coursenotes.«01-Lean».«08-DependentTypes»}

{include 0  «Leancourse».Coursenotes.«01-Lean».«09-Equality»}

{include 0  «Leancourse».Coursenotes.«01-Lean».«10-Proving»}

{include 0  «Leancourse».Coursenotes.«01-Lean».«11-Exploring»}

{include 0  «Leancourse».Coursenotes.«01-Lean».«12-Notation»}
