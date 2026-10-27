import VersoManual

import «Leancourse».Coursenotes.«1-Lean».«1-Nat»
import «Leancourse».Coursenotes.«1-Lean».«2-Types»
import «Leancourse».Coursenotes.«1-Lean».«3-Rules»
import «Leancourse».Coursenotes.«1-Lean».«4-Terms»
import «Leancourse».Coursenotes.«1-Lean».«5-Typeclasses»
import «Leancourse».Coursenotes.«1-Lean».«6-CurryHoward»
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
Two chapters on types follow: first how types are built —
function types, `inductive` types and structures, pairs, subtypes,
quotients and the universe hierarchy — and then the rules behind
them, with `Prop`.  After that come terms and the typeclass system, the
Curry-Howard correspondence tying propositions to types and proofs to
terms, and notation.
(Several reference topics — the alphabetical tactic glossary, how a
Lean file is organized, Lean's brackets, equality and reduction, the
diagnostic commands, and Navigating Mathlib — are covered in the
{ref "appendix"}[Appendix]; the deeper foundations, the axioms of Lean
and well-foundedness, are treated in the *Mathematics* part.)

{include 0  «Leancourse».Coursenotes.«1-Lean».«1-Nat»}

{include 0  «Leancourse».Coursenotes.«1-Lean».«2-Types»}

{include 0  «Leancourse».Coursenotes.«1-Lean».«3-Rules»}

{include 0  «Leancourse».Coursenotes.«1-Lean».«4-Terms»}

{include 0  «Leancourse».Coursenotes.«1-Lean».«5-Typeclasses»}

{include 0  «Leancourse».Coursenotes.«1-Lean».«6-CurryHoward»}

{include 0  «Leancourse».Coursenotes.«1-Lean».«7-Notation»}
