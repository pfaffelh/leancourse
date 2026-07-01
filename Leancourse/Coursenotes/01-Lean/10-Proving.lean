import VersoManual
import Manual.Meta
import Leancourse.Misc.Defs
import Mathlib

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open MyDef

set_option pp.rawOnError true

#doc (Manual) "Proving propositions" =>
%%%
htmlSplit := .never
tag := "proof"
%%%

# Types as theorems, terms as proofs
%%%
tag := "foundation"
%%%

Recall from the {ref "curry-howard"}[Curry-Howard chapter] that a
*proposition* is itself a type (living in the universe `Prop`) whose
*terms* are its *proofs*, and that such a term is built either
directly (*term mode*) or step by step after `by` (*tactic mode*).
This chapter is the practical bridge to the exercises: it revisits
that picture on a real open problem and points you at the tactics you
will actually use.

Proving a statement means *constructing a term* of the corresponding
type.  For instance, Goldbach's conjecture is a term of type `Prop`:

```lean
theorem goldbach : ∀ (n : ℕ) (h₁ : n > 2) (h₂ : Even n),
    ∃ (i j : ℕ), (Prime i) ∧ (Prime j) ∧ (n = i + j) := by
  sorry
```

A term of this type -- something that would replace the `sorry` --
*is* a proof of the conjecture.  Hence the slogan:

*Types as theorems, terms as proofs!*

Constructing a term of type `ℕ` is easy (`0 : ℕ` will do);
constructing a term of the Goldbach type would require actually
proving the conjecture.  (For the type universes this rests on --
`Prop`, `Type`, and why there is no "type of all types" -- see the
foundations in the *Mathematics* part.)

# Which tactics, and where to find them
%%%
tag := "firststeps"
%%%

The core tactics you meet first are `intro`, `exact`, `apply`, `rw`,
`have`, `obtain`, `refine`, and `use`, together with the
library-search helpers `apply?` and `simp?`.  Rather than tabulate
them here, we introduce each one *hands-on in the exercises*, right
where you first need it -- so you can experiment immediately.  The
complete alphabetical reference, with many more tactics, lives in the
{ref "tactics"}[Tactics] appendix, and searching Mathlib for the
right lemma is covered in {ref "navigating-mathlib"}[Navigating
Mathlib].

# Exercises
%%%
tag := "exercises"
%%%

It is now time to move to the exercises.  Proceed to `vscode` (or
`gitpod`), copy the exercises folder, and start coding.  Each sheet
introduces the tactics it needs; the {ref "tactics"}[Tactics]
appendix gives the alphabetical reference.
