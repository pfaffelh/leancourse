import VersoManual

import «Leancourse».Coursenotes.«2-Mathematics».«1-Numbers»
import «Leancourse».Coursenotes.«2-Mathematics».«2-SetsAndTypes»
import «Leancourse».Coursenotes.«2-Mathematics».«3-Foundations»
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

This part opens with the number systems, each of them one of the type
formers of the Lean part, and with the vocabulary of sets; then come
the foundations — universes, the axioms of Lean, well-foundedness and
the avoidance of paradoxes. After that it surveys parts of Mathlib
that go beyond first-year mathematics: order theory and lattices, the
algebraic hierarchy, filters as a unifying language for limits,
topology and measure theory, and discrete probability.  The aim is not
to redo the mathematics from scratch but to show how Mathlib organizes
it — which typeclasses to use, where to find the lemmas, and what the
design trade-offs were.

Each chapter starts with a short notation table so the symbols are
introduced before they appear, and uses Verso's `{docstring}` block
to render Mathlib definitions and lemmas inline so the notes stay in
sync with the library.

{include 0 «Leancourse».Coursenotes.«2-Mathematics».«1-Numbers»}

{include 0 «Leancourse».Coursenotes.«2-Mathematics».«2-SetsAndTypes»}

{include 0 «Leancourse».Coursenotes.«2-Mathematics».«3-Foundations»}

{include 0 «Leancourse».Coursenotes.«2-Mathematics».«4-OrdersAndLattices»}

{include 0 «Leancourse».Coursenotes.«2-Mathematics».«5-AlgebraicHierarchy»}

{include 0 «Leancourse».Coursenotes.«2-Mathematics».«6-Filters»}

{include 0 «Leancourse».Coursenotes.«2-Mathematics».«7-Topology»}

{include 0 «Leancourse».Coursenotes.«2-Mathematics».«8-MeasureTheory»}

{include 0 «Leancourse».Coursenotes.«2-Mathematics».«9-Probability»}
