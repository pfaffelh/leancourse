import VersoManual

import «Leancourse».Coursenotes.«03-Mathematics».«01-OrdersAndLattices»
import «Leancourse».Coursenotes.«03-Mathematics».«02-AlgebraicHierarchy»
import «Leancourse».Coursenotes.«03-Mathematics».«03-Filters»
import «Leancourse».Coursenotes.«03-Mathematics».«04-Topology»
import «Leancourse».Coursenotes.«03-Mathematics».«05-MeasureTheory»
import «Leancourse».Coursenotes.«03-Mathematics».«06-Probability»

open Verso.Genre Manual

#doc (Manual) "Advanced Mathematics" =>
%%%
htmlSplit := .never
tag := "advanced-mathematics"
%%%

This part surveys parts of Mathlib that go beyond first-year
mathematics: order theory and lattices, the algebraic hierarchy,
filters as a unifying language for limits, topology and measure
theory, and discrete probability.  The aim is not to redo the
mathematics from scratch but to show how Mathlib organizes it -- which
typeclasses to use, where to find the lemmas, and what the design
trade-offs were.

Each chapter starts with a short notation table so the symbols are
introduced before they appear, and uses Verso's `{docstring}` block
to render Mathlib definitions and lemmas inline so the notes stay in
sync with the library.

{include 0 «Leancourse».Coursenotes.«03-Mathematics».«01-OrdersAndLattices»}

{include 0 «Leancourse».Coursenotes.«03-Mathematics».«02-AlgebraicHierarchy»}

{include 0 «Leancourse».Coursenotes.«03-Mathematics».«03-Filters»}

{include 0 «Leancourse».Coursenotes.«03-Mathematics».«04-Topology»}

{include 0 «Leancourse».Coursenotes.«03-Mathematics».«05-MeasureTheory»}

{include 0 «Leancourse».Coursenotes.«03-Mathematics».«06-Probability»}
