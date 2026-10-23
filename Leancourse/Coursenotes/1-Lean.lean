import VersoManual

import «Leancourse».Coursenotes.«1-Lean».«1-Nat»
import «Leancourse».Coursenotes.«1-Lean».«2-Types»
import «Leancourse».Coursenotes.«1-Lean».«3-Terms»
import «Leancourse».Coursenotes.«1-Lean».«4-Typeclasses»
import «Leancourse».Coursenotes.«1-Lean».«5-CurryHoward»
import «Leancourse».Coursenotes.«1-Lean».«6-DependentTypes»
import «Leancourse».Coursenotes.«1-Lean».«7-Notation»

open Verso.Genre Manual

#doc (Manual) "Lean and its type theory" =>
%%%
htmlSplit := .never
tag := "lean"
%%%

This part covers Lean both as a practical proof assistant and as the
dependent type theory it is built on.  We begin with the natural
numbers — which comes with its *constructors* as well as with reduction rules.
We then turn to types and the universe hierarchy — including how to
define your own types with `inductive` and `structure` — then
functions and terms and the typeclass system.  Finally comes the
theory: the Curry-Howard correspondence tying propositions to types
and proofs to terms (and, with it, how to prove things interactively),
dependent types, and notation.
(Several reference topics — the alphabetical tactic glossary, how a
Lean file is organized, Lean's brackets, equality and reduction, the
diagnostic commands, and Navigating Mathlib — are covered in the
{ref "appendix"}[Appendix]; the deeper foundations, the axioms of Lean
and well-foundedness, are treated in the *Mathematics* part.)

{include 0  «Leancourse».Coursenotes.«1-Lean».«1-Nat»}

{include 0  «Leancourse».Coursenotes.«1-Lean».«2-Types»}

{include 0  «Leancourse».Coursenotes.«1-Lean».«3-Terms»}

{include 0  «Leancourse».Coursenotes.«1-Lean».«4-Typeclasses»}

{include 0  «Leancourse».Coursenotes.«1-Lean».«5-CurryHoward»}

{include 0  «Leancourse».Coursenotes.«1-Lean».«6-DependentTypes»}

{include 0  «Leancourse».Coursenotes.«1-Lean».«7-Notation»}
