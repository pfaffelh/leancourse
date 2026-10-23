import VersoManual

open Verso.Genre Manual

#doc (Manual) "Organization" =>
%%%
tag := "organization"
file := "Organization"
htmlSplit := .never
%%%

What happens when, what the short tests are for, the slides, and the
recordings. Winter term 2026/27, University of Freiburg.

Lecture Monday, lab Wednesday, 90 minutes each. The lecture starts on
19 October 2026 and ends on 10 February 2027, with a break from
23 December to 6 January. The break costs three Wednesdays but only
two Mondays, so there are 15 lectures and 14 labs: **Monday 21
December has no lab.**

# What comes when
%%%
tag := "schedule"
%%%

Sheets are named after the chapter they belong to, so `2.6-b` is the
second sheet on chapter 2.6. `L-a` to `L-g` are the logic block, which
belongs to no chapter and runs alongside the first five weeks; `A-a`
and `A-b` are the appendix, `X-a` an extra sheet.

:::table (align := left) +header
* + W
  + Mon
  + Wed
  + Lecture
  + Chapter
  + Sheets
* + 1
  + 19.10.
  + 21.10.
  + Why formalize? *Wed: installation*
  + {ref "introduction"}[Introduction]
  + `L-a`
* + 2
  + 26.10.
  + 28.10.
  + `Nat`, `Bool`, reduction rules
  + {ref "nat"}[1.1]
  + `L-b`, `L-c`, `1.1-a`
* + 3
  + 02.11.
  + 04.11.
  + Types, inductive types, quotients
  + {ref "types"}[1.2]
  + `L-d`, `1.2-a`, `1.1-b`
* + 4
  + 09.11.
  + 11.11.
  + Terms and pattern matching · **test 1**
  + {ref "terms"}[1.3]
  + `L-e`, `L-f`, `1.1-c`
* + 5
  + 16.11.
  + 18.11.
  + Typeclasses
  + {ref "typeclasses"}[1.4]
  + `L-g`, `1.4-a`, `1.4-b`, extra `X-a`
* + 6
  + 23.11.
  + 25.11.
  + Curry-Howard
  + {ref "curry-howard"}[1.5]
  + `1.5-a`, `1.5-b`
* + 7
  + 30.11.
  + 02.12.
  + Dependent types and notation · **test 2**
  + {ref "dependent-types"}[1.6], {ref "notation"}[1.7]
  + `1.6-a`, `1.7-a`
* + 8
  + 07.12.
  + 09.12.
  + Sets and types; well-foundedness
  + {ref "sets-and-types"}[2.1], {ref "logic-wf"}[2.3]
  + `2.1-a`, `2.1-b`, `2.1-c`
* + 9
  + 14.12.
  + 16.12.
  + Universes and axioms · **test 3**
  + {ref "universes-axioms"}[2.2]
  + `2.2-a`, `2.3-a`
* + 10
  + 21.12.
  + --
  + Proof engineering; `conv`
  + {ref "tactics"}[Appendix]
  + `A-a`, `A-b`
* + 11
  + 11.01.
  + 13.01.
  + Orders, the algebraic hierarchy
  + {ref "orders-and-lattices"}[2.4], {ref "algebraic-hierarchy-mathlib"}[2.5]
  + `2.4-a`, `2.5-a`
* + 12
  + 18.01.
  + 20.01.
  + Filters
  + {ref "filters"}[2.6]
  + `2.6-a`, `2.6-b`
* + 13
  + 25.01.
  + 27.01.
  + Topology · **test 4**
  + {ref "topology"}[2.7]
  + `2.7-a`
* + 14
  + 01.02.
  + 03.02.
  + Measure theory
  + {ref "measure-theory"}[2.8]
  + `2.8-a`
* + 15
  + 08.02.
  + 10.02.
  + Monads and probability · **test 5**
  + {ref "probability-pmf"}[2.9]
  + `2.9-a`, `2.9-b`
:::

The logic block runs ahead of its theory on purpose: you prove things
by hand in weeks 2 to 5 and read why they work in chapters 1.5 and
2.2. `A-a` and `A-b` are holiday work over the break.

The individual projects come after the fifteen weeks, in the lecture-free
period; see the {ref "projects"}[Projects chapter].

# The short tests
%%%
tag := "short-tests"
%%%

Five tests, 20 minutes each, at the start of the lab, on paper.
**Three of the five must be passed** to be admitted to the oral exam.
A test is passed when two of its three questions are right. A test not
taken counts as not passed.

Dates: **11.11., 02.12., 16.12., 27.01., 10.02.**

The tests exist because the homework cannot tell us anything. Using AI
on the sheets is allowed, and in any case Lean's own `grind` proves
127 of the 128 statements of the logic block with one call and no
arguments. A correct submission is therefore a sign of participation
and nothing more. Admission has to rest on something else, and twenty
minutes on paper every third week is the cheapest honest thing we
could think of.

What is tested is the proof state and understanding, not syntax and
not lemma names -- looking those up is what `exact?` is for. Typical
questions:

* The state is `h : P ∧ Q`, the goal `⊢ R`. You write
  `obtain ⟨hP, hQ⟩ := h`. What does the state look like afterwards?
* Is `¬(P ∧ Q) → (¬P ∨ ¬Q)` provable constructively? If not, where
  does the excluded middle come in?
* This proof fails with "no binders to introduce". Why?

The {ref "cheatsheet"}[cheatsheet] is exactly this format, and sheet
`L-g` teaches you to check the second kind of question yourself, by
running `itauto` against `tauto`.

# Slides
%%%
tag := "slides"
%%%

Some chapters have a deck, used in the lecture and readable on its
own.  The figures and claims are those of the text, so either can be
used without the other.

* [Why formalize?](slides/0-introduction/) — the first lecture: what
  formalizing means, where things stand in 2026, the four episodes and
  the landmark formalizations.
* Lean and its type theory, one deck per chapter:
  * [The natural numbers and reduction rules](slides/1-1-nat/) —
    {ref "nat"}[chapter]
  * [Types](slides/1-2-types/) — {ref "types"}[chapter]
  * [Terms](slides/1-3-terms/) — {ref "terms"}[chapter]
  * [Typeclasses](slides/1-4-typeclasses/) — {ref "typeclasses"}[chapter]
  * [Propositions and proofs](slides/1-5-curry-howard/) —
    {ref "curry-howard"}[chapter]
  * [Dependent types in depth](slides/1-6-dependent-types/) —
    {ref "dependent-types"}[chapter]
  * [Notation and abbreviations](slides/1-7-notation/) —
    {ref "notation"}[chapter]
* [Filters in Mathlib](slides/2-6-filters/) — accompanies the
  {ref "filters"}[chapter on filters].

Press `s` in a deck for the speaker notes, `o` for an overview of all
slides, and `?` for the remaining keys.  Every slide carries a link in
its upper right corner that leads back to this page.

# Recordings
%%%
tag := "recordings"
%%%

The lectures are recorded and published on
[*Formally proven*](https://www.youtube.com/channel/UCdCtAPNg3baUKSOT5YY28BA), the course's YouTube channel. Each
recording carries chapter marks that follow the slides, so a single
topic can be found without watching the whole hour.

The exercise sheets are worked through on the same channel, one video
per sheet. Each video description links to the sheet on GitHub and to
a version that runs in the browser, so nothing has to be installed to
follow along.
