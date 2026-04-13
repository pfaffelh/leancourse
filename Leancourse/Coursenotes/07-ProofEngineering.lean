import VersoManual

import «Leancourse».Coursenotes.«07-ProofEngineering».«01-Automation»
import «Leancourse».Coursenotes.«07-ProofEngineering».«02-NavigatingMathlib»
import «Leancourse».Coursenotes.«07-ProofEngineering».«03-CommonPitfalls»

open Verso.Genre Manual

#doc (Manual) "Proof Engineering" =>
%%%
htmlSplit := .never
tag := "proof-engineering"
%%%

Once you can finish small proofs by hand, the next skill is working
*efficiently* with a library the size of Mathlib.  This part collects
the techniques that experienced users rely on every day:

- *Automation*: high-powered tactics (`simp`, `aesop`, `polyrith`,
  `decide`, `omega`, ...) that close routine goals so you can focus
  on the interesting steps.
- *Navigating Mathlib*: how to find the right lemma -- by name, by
  type signature (`exact?`, `apply?`, Loogle, Moogle), or by
  browsing the source.
- *Common pitfalls*: typeclass diamonds, `Nat`-vs-`Int` coercions,
  the `≤`-vs-`≥` convention, definitional unfolding, and other things
  that catch first-time users.

{include 0 «Leancourse».Coursenotes.«07-ProofEngineering».«01-Automation»}

{include 0 «Leancourse».Coursenotes.«07-ProofEngineering».«02-NavigatingMathlib»}

{include 0 «Leancourse».Coursenotes.«07-ProofEngineering».«03-CommonPitfalls»}
