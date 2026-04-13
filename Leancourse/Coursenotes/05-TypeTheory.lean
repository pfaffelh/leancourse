import VersoManual

import «Leancourse».Coursenotes.«05-TypeTheory».«01-CurryHoward»
import «Leancourse».Coursenotes.«05-TypeTheory».«02-DependentTypes»
import «Leancourse».Coursenotes.«05-TypeTheory».«03-UniversesAndAxioms»

open Verso.Genre Manual

#doc (Manual) "Type Theory" =>
%%%
htmlSplit := .never
tag := "type-theory"
%%%

Lean's foundation is _dependent type theory_.  Every term has a type;
every proof is a term whose type is the proposition it proves.  This
part unpacks the consequences of that single design choice:

- _Curry-Howard_: how propositions become types and proofs become
  terms, so that `→` is both function arrow and implication.
- _Dependent types_: types that depend on values, giving us `Σ`, `Π`,
  `Subtype`, `Vector n`, and the rest of Lean's type-level vocabulary.
- _Universes and axioms_: why `Type` cannot contain itself, and which
  axioms (`funext`, `propext`, `Classical.choice`) Lean adds on top
  of the kernel.

The material here is theoretical: very little new tactic vocabulary,
but a clearer view of why everything in earlier chapters works.

{include 0 «Leancourse».Coursenotes.«05-TypeTheory».«01-CurryHoward»}

{include 0 «Leancourse».Coursenotes.«05-TypeTheory».«02-DependentTypes»}

{include 0 «Leancourse».Coursenotes.«05-TypeTheory».«03-UniversesAndAxioms»}
