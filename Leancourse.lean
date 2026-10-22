-- This module serves as the root of the `Leancourse` library.
-- Import modules here that should be built as part of the library.
import VersoManual
import Manual.Meta
import Mathlib

import «Leancourse».Coursenotes.«00-Introduction»
import «Leancourse».Coursenotes.«01-Lean»
import «Leancourse».Coursenotes.«02-Mathematics»
import «Leancourse».Coursenotes.«03-Projects»
import «Leancourse».Coursenotes.«04-Appendix»
import «Leancourse».Coursenotes.«05-Slides»
import «Leancourse».Coursenotes.«99-Bibliography»

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

#doc (Manual) "Interactive Theorem Proving using Lean, Winter 2026/27" =>
%%%
tag := "ITPFr"
authors := ["Peter Pfaffelhuber"]
%%%

Notes for a course on formal proving with the interactive theorem prover Lean 4 (below simply Lean), winter semester 2026/27, University of Freiburg. Start with the {ref "introduction"}[Introduction]; hardware, installation and the run of the semester are at its end.

{include 0 «Leancourse».Coursenotes.«00-Introduction»}

{include 0 «Leancourse».Coursenotes.«01-Lean»}

{include 0 «Leancourse».Coursenotes.«02-Mathematics»}

{include 0 «Leancourse».Coursenotes.«03-Projects»}

{include 0 «Leancourse».Coursenotes.«04-Appendix»}

{include 0 «Leancourse».Coursenotes.«05-Slides»}

{include 0 «Leancourse».Coursenotes.«99-Bibliography»}
