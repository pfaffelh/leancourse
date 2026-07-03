import VersoManual

import «Leancourse».Coursenotes.«01-Lean».«01-Types»
import «Leancourse».Coursenotes.«01-Lean».«02-Functions»
import «Leancourse».Coursenotes.«01-Lean».«03-Typeclasses»
import «Leancourse».Coursenotes.«01-Lean».«04-Parentheses»
import «Leancourse».Coursenotes.«01-Lean».«05-CurryHoward»
import «Leancourse».Coursenotes.«01-Lean».«06-DependentTypes»
import «Leancourse».Coursenotes.«01-Lean».«07-Equality»
import «Leancourse».Coursenotes.«01-Lean».«08-Notation»

open Verso.Genre Manual

#doc (Manual) "Lean and its type theory" =>
%%%
htmlSplit := .never
tag := "lean"
%%%

This part covers Lean both as a practical proof assistant and as the
dependent type theory it is built on.  We begin with types and the
universe hierarchy -- including how to define your own types with
`inductive` and `structure` -- then functions and terms, the typeclass
system, and Lean's various brackets.  We then turn to the theory: the
Curry-Howard correspondence tying propositions to types and proofs to
terms (and, with it, how to prove things interactively), dependent
types, and equality.  The final chapter covers notation.
(The {ref "tactics"}[alphabetical tactic glossary] and
{ref "navigating-mathlib"}[Navigating Mathlib] live in the Appendix;
the deeper foundations -- the axioms of Lean and well-foundedness --
are treated in the *Mathematics* part.)

{include 0  «Leancourse».Coursenotes.«01-Lean».«01-Types»}

{include 0  «Leancourse».Coursenotes.«01-Lean».«02-Functions»}

{include 0  «Leancourse».Coursenotes.«01-Lean».«03-Typeclasses»}

{include 0  «Leancourse».Coursenotes.«01-Lean».«04-Parentheses»}

{include 0  «Leancourse».Coursenotes.«01-Lean».«05-CurryHoward»}

{include 0  «Leancourse».Coursenotes.«01-Lean».«06-DependentTypes»}

{include 0  «Leancourse».Coursenotes.«01-Lean».«07-Equality»}

{include 0  «Leancourse».Coursenotes.«01-Lean».«08-Notation»}
