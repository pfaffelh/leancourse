-- This module serves as the root of the `Leancourse` library.
-- Import modules here that should be built as part of the library.
import VersoManual
import Manual.Meta
import Mathlib

import «Leancourse».Coursenotes.«0-Introduction»
import «Leancourse».Coursenotes.«1-Lean»
import «Leancourse».Coursenotes.«2-Mathematics»
import «Leancourse».Coursenotes.«3-Projects»
import «Leancourse».Coursenotes.«4-Appendix»
import «Leancourse».Coursenotes.«5-Organization»
import «Leancourse».Coursenotes.«9-Bibliography»

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

#doc (Manual) "Interactive Theorem Proving using Lean, Winter 2026/27" =>
%%%
tag := "ITPFr"
authors := ["Peter Pfaffelhuber"]
%%%

Notes for a course on formal proving with the interactive theorem prover Lean 4 (below simply Lean), winter semester 2026/27, University of Freiburg. Start with the {ref "introduction"}[Introduction]; hardware, installation and the run of the semester are at its end.

{include 0 «Leancourse».Coursenotes.«0-Introduction»}

{include 0 «Leancourse».Coursenotes.«1-Lean»}

{include 0 «Leancourse».Coursenotes.«2-Mathematics»}

{include 0 «Leancourse».Coursenotes.«3-Projects»}

{include 0 «Leancourse».Coursenotes.«4-Appendix»}

{include 0 «Leancourse».Coursenotes.«5-Organization»}

{include 0 «Leancourse».Coursenotes.«9-Bibliography»}
