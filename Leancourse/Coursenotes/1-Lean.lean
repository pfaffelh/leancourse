import VersoManual

import «Leancourse».Coursenotes.«1-Lean».«1-Nat»
import «Leancourse».Coursenotes.«1-Lean».«2-FunctionsInductiveStructures»
import «Leancourse».Coursenotes.«1-Lean».«3-PatternMatchingRecursion»
import «Leancourse».Coursenotes.«1-Lean».«4-PairsSubtypesQuotients»
import «Leancourse».Coursenotes.«1-Lean».«5-Rules»
import «Leancourse».Coursenotes.«1-Lean».«6-Typeclasses»
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
Then come the types, built together with their terms: universes,
function types, `inductive` types and structures; the functions on
inductive types, defined by pattern matching and recursion; dependent
pairs, subtypes, type families, propositions as types, and quotients.
A last chapter on types gives the rules behind them, with `Prop`.
After that come the typeclass system and notation.
(Several reference topics — the alphabetical tactic glossary, how a
Lean file is organized, Lean's brackets, equality and reduction, the
diagnostic commands, and Navigating Mathlib — are covered in the
{ref "appendix"}[Appendix]; the deeper foundations, the axioms of Lean
and well-foundedness, are treated in the *Mathematics* part.)

{include 0  «Leancourse».Coursenotes.«1-Lean».«1-Nat»}

{include 0  «Leancourse».Coursenotes.«1-Lean».«2-FunctionsInductiveStructures»}

{include 0  «Leancourse».Coursenotes.«1-Lean».«3-PatternMatchingRecursion»}

{include 0  «Leancourse».Coursenotes.«1-Lean».«4-PairsSubtypesQuotients»}

{include 0  «Leancourse».Coursenotes.«1-Lean».«5-Rules»}

{include 0  «Leancourse».Coursenotes.«1-Lean».«6-Typeclasses»}


{include 0  «Leancourse».Coursenotes.«1-Lean».«7-Notation»}
