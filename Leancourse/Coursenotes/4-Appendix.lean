import VersoManual

import «Leancourse».Coursenotes.«4-Appendix».«1-Tactics»
import «Leancourse».Coursenotes.«4-Appendix».«2-FileStructure»
import «Leancourse».Coursenotes.«4-Appendix».«3-NavigatingMathlib»
import «Leancourse».Coursenotes.«4-Appendix».«4-CommonPitfalls»
import «Leancourse».Coursenotes.«4-Appendix».«5-SmallReferenceTopics»

open Verso.Genre Manual

#doc (Manual) "Appendix" =>
%%%
htmlSplit := .never
tag := "appendix"
%%%

Reference material to consult as needed: the alphabetical glossary of
tactics; how a Lean file is organized (imports, namespaces, sections,
and scoping); how to navigate and search Mathlib; common pitfalls; and
a collection of short reference topics — Lean's different brackets,
the kinds of equality, exploring definitions with `#check`/`#print`,
the kernel and the elaborator, the diagnostic commands, and an alphabetical keyword reference.

{include 0 «Leancourse».Coursenotes.«4-Appendix».«1-Tactics»}

{include 0 «Leancourse».Coursenotes.«4-Appendix».«2-FileStructure»}

{include 0 «Leancourse».Coursenotes.«4-Appendix».«3-NavigatingMathlib»}

{include 0 «Leancourse».Coursenotes.«4-Appendix».«4-CommonPitfalls»}

{include 0 «Leancourse».Coursenotes.«4-Appendix».«5-SmallReferenceTopics»}
