/-
Bibliography database for the course notes.

This module plays the role of a `.bib` file: it defines the citable
references as values.  Cite them inline with the `{citet ...}[]`,
`{citep ...}[]`, or `{citehere ...}[]` roles, and list them in the
Bibliography appendix with `{citehere ...}[]`.

Only the entry types `Article`, `InProceedings`, `Thesis`, and
`ArXiv` are provided by Verso, so books and online resources are kept
as ordinary links in the text rather than as formal entries here.
-/
import VersoManual

open Verso Verso.Genre Manual

namespace Leancourse.Refs

/--
A `@misc`-style entry (book, lecture notes, online resource).

Verso's `Citable` has no `Book`/`Misc`/`Online` constructor, so we
model such sources as an `InProceedings`: the `howpublished` text
(publisher, "Lecture notes", a website, ...) goes in the `booktitle`
field and is rendered after the word "In".
-/
def misc (title : Doc.Inline Manual)
    (authors : Array (Doc.Inline Manual)) (year : Int)
    (howpublished : Doc.Inline Manual)
    (url : Option String := none) : InProceedings where
  title := title
  authors := authors
  year := year
  booktitle := howpublished
  url := url

def cohenEtAl2018 : ArXiv where
  title := inlines!"Cubical Type Theory: A Constructive Interpretation of the Univalence Axiom"
  authors := #[inlines!"Cyril Cohen", inlines!"Thierry Coquand",
    inlines!"Simon Huber", inlines!"Anders Mörtberg"]
  year := 2018
  id := "1611.02108"

def coquandHuet1988 : Article where
  title := inlines!"The Calculus of Constructions"
  authors := #[inlines!"Thierry Coquand", inlines!"Gérard Huet"]
  journal := inlines!"Information and Computation"
  year := 1988
  month := none
  volume := inlines!"76"
  number := inlines!"2–3"
  pages := some (95, 120)
  url := some "https://doi.org/10.1016/0890-5401(88)90005-3"

def coquandPaulin1990 : InProceedings where
  title := inlines!"Inductively Defined Types"
  authors := #[inlines!"Thierry Coquand", inlines!"Christine Paulin-Mohring"]
  year := 1990
  booktitle := inlines!"COLOG-88"
  series := some inlines!"Lecture Notes in Computer Science 417"
  url := some "https://doi.org/10.1007/3-540-52335-9_47"

def girard1972 : Thesis where
  title := inlines!"Interprétation fonctionnelle et élimination des coupures de l'arithmétique d'ordre supérieur"
  author := inlines!"Jean-Yves Girard"
  year := 1972
  university := inlines!"Université Paris VII"
  degree := inlines!"PhD thesis"

def leanSystem2015 : InProceedings where
  title := inlines!"The Lean Theorem Prover (System Description)"
  authors := #[inlines!"Leonardo de Moura", inlines!"Soonho Kong",
    inlines!"Jeremy Avigad", inlines!"Floris van Doorn",
    inlines!"Jakob von Raumer"]
  year := 2015
  booktitle := inlines!"Automated Deduction – CADE-25"
  series := some inlines!"Lecture Notes in Computer Science 9195"
  url := some "https://doi.org/10.1007/978-3-319-21401-6_26"

def lean4_2021 : InProceedings where
  title := inlines!"The Lean 4 Theorem Prover and Programming Language"
  authors := #[inlines!"Leonardo de Moura", inlines!"Sebastian Ullrich"]
  year := 2021
  booktitle := inlines!"Automated Deduction – CADE 28"
  series := some inlines!"Lecture Notes in Computer Science 12699"
  url := some "https://doi.org/10.1007/978-3-030-79876-5_37"

def martinLof1975 : InProceedings where
  title := inlines!"An Intuitionistic Theory of Types: Predicative Part"
  authors := #[inlines!"Per Martin-Löf"]
  year := 1975
  booktitle := inlines!"Logic Colloquium '73"
  series := some inlines!"Studies in Logic and the Foundations of Mathematics 80"
  url := some "https://doi.org/10.1016/S0049-237X(08)71945-1"

def mathlib2020 : InProceedings where
  title := inlines!"The Lean Mathematical Library"
  authors := #[inlines!"The mathlib Community"]
  year := 2020
  booktitle := inlines!"CPP 2020: Proceedings of the 9th ACM SIGPLAN International Conference on Certified Programs and Proofs"
  url := some "https://doi.org/10.1145/3372885.3373824"

/-! ### `@misc`-style entries (books, lecture notes, online) -/

def hottBook : InProceedings := misc
  (title := inlines!"Homotopy Type Theory: Univalent Foundations of Mathematics")
  (authors := #[inlines!"The Univalent Foundations Program"])
  (year := 2013)
  (howpublished := inlines!"Institute for Advanced Study")
  (url := some "https://homotopytypetheory.org/book/")

def buzzardMehta : InProceedings := misc
  (title := inlines!"Formalising Mathematics")
  (authors := #[inlines!"Kevin Buzzard", inlines!"Bhavik Mehta"])
  (year := 2024)
  (howpublished := inlines!"Lecture notes, Imperial College London")
  (url := some "https://github.com/ImperialCollegeLondon/formalising-mathematics-2024")

def theoremProvingInLean4 : InProceedings := misc
  (title := inlines!"Theorem Proving in Lean 4")
  (authors := #[inlines!"Jeremy Avigad", inlines!"Leonardo de Moura",
    inlines!"Soonho Kong", inlines!"Sebastian Ullrich"])
  (year := 2024)
  (howpublished := inlines!"Online textbook")
  (url := some "https://leanprover.github.io/theorem_proving_in_lean4/")

def mathlibDocs : InProceedings := misc
  (title := inlines!"Mathlib Documentation")
  (authors := #[inlines!"The mathlib Community"])
  (year := 2025)
  (howpublished := inlines!"Online API documentation")
  (url := some "https://leanprover-community.github.io/mathlib4_docs/")

end Leancourse.Refs
