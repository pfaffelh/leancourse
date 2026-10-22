import VersoManual

open Verso.Genre Manual

#doc (Manual) "Slides" =>
%%%
tag := "slides"
file := "Lecture-slides"
%%%

Some chapters have a deck, used in the lecture and readable on its
own.  The figures and claims are those of the text, so either can be
used without the other.

* [Why formalize?](slides/introduction/) — the first lecture: what
  formalizing means, where things stand in 2026, the four episodes and
  the landmark formalizations.
* Lean and its type theory, one deck per chapter:
  * [The natural numbers and reduction rules](slides/nat/) —
    {ref "nat"}[chapter]
  * [Types](slides/types/) — {ref "types"}[chapter]
  * [Terms](slides/terms/) — {ref "terms"}[chapter]
  * [Typeclasses](slides/typeclasses/) — {ref "typeclasses"}[chapter]
  * [Propositions and proofs](slides/curry-howard/) —
    {ref "curry-howard"}[chapter]
  * [Dependent types in depth](slides/dependent-types/) —
    {ref "dependent-types"}[chapter]
  * [Notation and abbreviations](slides/notation/) —
    {ref "notation"}[chapter]
* [Filters in Mathlib](slides/filters/) — accompanies the
  {ref "filters"}[chapter on filters].

The lectures are recorded and published on
[*Formally proven*](https://www.youtube.com/channel/UCdCtAPNg3baUKSOT5YY28BA), the course's YouTube channel. Each
recording carries chapter marks that follow the slides, so a single
topic can be found without watching the whole hour.

Press `s` in a deck for the speaker notes, `o` for an overview of all
slides, and `?` for the remaining keys.  Every slide carries a link in
its upper right corner that leads back to this page.
