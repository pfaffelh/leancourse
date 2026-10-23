import VersoManual

import «Leancourse».Coursenotes.«2-Mathematics».«1-SetsAndTypes»
import «Leancourse».Coursenotes.«2-Mathematics».«2-UniversesAndAxioms»
import «Leancourse».Coursenotes.«2-Mathematics».«3-Logic»
import «Leancourse».Coursenotes.«2-Mathematics».«4-OrdersAndLattices»
import «Leancourse».Coursenotes.«2-Mathematics».«5-AlgebraicHierarchy»
import «Leancourse».Coursenotes.«2-Mathematics».«6-Filters»
import «Leancourse».Coursenotes.«2-Mathematics».«7-Topology»
import «Leancourse».Coursenotes.«2-Mathematics».«8-MeasureTheory»
import «Leancourse».Coursenotes.«2-Mathematics».«9-Probability»

open Verso.Genre Manual

#doc (Manual) "Mathematics" =>
%%%
htmlSplit := .never
tag := "advanced-mathematics"
%%%

This part opens with the foundations — the everyday vocabulary
(propositions, proofs, and sets), the universes and axioms on which
Lean's mathematics rests, and well-foundedness and the avoidance of
paradoxes — and then surveys parts of Mathlib that go beyond
first-year mathematics: order theory and lattices, the algebraic
hierarchy, filters as a unifying language for limits, topology and
measure theory, and discrete probability.  The aim is not to redo the
mathematics from scratch but to show how Mathlib organizes it — which
typeclasses to use, where to find the lemmas, and what the design
trade-offs were.

Each chapter starts with a short notation table so the symbols are
introduced before they appear, and uses Verso's `{docstring}` block
to render Mathlib definitions and lemmas inline so the notes stay in
sync with the library.

{include 0 «Leancourse».Coursenotes.«2-Mathematics».«1-SetsAndTypes»}

{include 0 «Leancourse».Coursenotes.«2-Mathematics».«2-UniversesAndAxioms»}

{include 0 «Leancourse».Coursenotes.«2-Mathematics».«3-Logic»}

{include 0 «Leancourse».Coursenotes.«2-Mathematics».«4-OrdersAndLattices»}

{include 0 «Leancourse».Coursenotes.«2-Mathematics».«5-AlgebraicHierarchy»}

{include 0 «Leancourse».Coursenotes.«2-Mathematics».«6-Filters»}

{include 0 «Leancourse».Coursenotes.«2-Mathematics».«7-Topology»}

{include 0 «Leancourse».Coursenotes.«2-Mathematics».«8-MeasureTheory»}

{include 0 «Leancourse».Coursenotes.«2-Mathematics».«9-Probability»}
