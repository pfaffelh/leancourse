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

Lecture Monday 16:15-17:45, lab Wednesday 16:15-17:45. The lecture starts on
19 October 2026 and ends on 10 February 2027, with a break from
23 December to 6 January.


# Slides
%%%
tag := "slides"
%%%

Most chapters have a deck, used in the lecture and readable on its
own.  The figures and claims are those of the text, so either can be
used without the other.

* [Why formalize?](slides/0-introduction/) — the first lecture: what
  formalizing means, where things stand in 2026, the four episodes and
  the landmark formalizations.
* [The natural numbers and reduction rules](slides/1-1-nat/) —
  {ref "nat"}[chapter 1.1]

A deck appears here when its chapter is taught.

Press `s` in a deck for the speaker notes, `o` for an overview of all
slides, and `?` for the remaining keys.  Every slide carries a link in
its upper right corner that leads back to this page.

# Recordings
%%%
tag := "recordings"
%%%

The lectures and lab sessions are recorded and published on
[*Formally proven*](https://www.youtube.com/channel/UCdCtAPNg3baUKSOT5YY28BA), the course's YouTube channel. Each
recording carries chapter marks that follow the slides, so a single
topic can be found without watching the whole hour.

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


# The short tests
%%%
tag := "short-tests"
%%%

Five tests, 20 minutes each, at the start of the lab, on paper.
**Three of the five must be passed** for the _Studienleistung_.
A test is passed when 50% of all points are achieved. A test not
taken counts as not passed.

Dates: **11.11., 02.12., 16.12., 27.01., 10.02.**

What is tested is the proof state and understanding. Here are some typical
questions:

* The state is `h : P ∧ Q`, the goal `⊢ R`. You write
  `obtain ⟨hP, hQ⟩ := h`. What does the state look like afterwards?
* Is `¬(P ∧ Q) → (¬P ∨ ¬Q)` provable constructively? If not, where
  does the excluded middle come in?
* This proof fails with "no binders to introduce". Why?

# Goals
%%%
tag := "goals"
%%%

The course is for mathematics students.

* *Reading formal statements.* Judging whether a formal statement says what the informal one claims ({ref "why-formalize"}[see above]).
* *Interactive theorem proving.* A small kernel checks every logical step of a proof, and the editor reports what remains to be proved as you write ({ref "term"}[the proof state]). This is not the older use of computers in mathematics, which was to work through many cases ({ref "four-colour-episode"}[the four colour theorem]).
* *Mathematical content.* The mathematics in the first half is deliberately easy, because explaining a proof to a computer requires understanding it first, and a proof of more than a few lines has to be planned so that the commands — {ref "tactics"}[*tactics*] — fit together. The second half goes deeper into the mathematics.
* *Functional programming.* {ref "inductive"}[Inductive types], {ref "structures"}[structures], {ref "typeclasses"}[typeclasses] and {ref "monads"}[monads], needed both to use Lean and to read *Mathlib*.
* *Type theory.* Lean rests on dependent type theory: the {ref "curry-howard"}[Curry-Howard correspondence], {ref "dependent-types"}[dependent types], the {ref "type-universes"}[universe hierarchy], and {ref "lean-axioms"}[Lean's axioms].
* *Mathematics in Mathlib.* How the library organizes {ref "orders-and-lattices"}[order theory], the {ref "algebraic-hierarchy-mathlib"}[algebraic hierarchy], {ref "filters"}[filters] (a single framework for limits), {ref "topology"}[topology], {ref "measure-theory"}[measure theory] and {ref "probability-pmf"}[discrete probability]. Textbooks rarely treat these from the point of view of formalization.
* *Proof engineering.* Automation tactics, {ref "navigating-mathlib"}[searching *Mathlib*], and the {ref "common-pitfalls"}[common pitfalls] of a large formal library.

# Getting Lean running
%%%
tag := "practical"
%%%

*Hardware.* Lean memory-maps all of *Mathlib* while it works, and every exercise sheet begins with `import Mathlib`. A two-line sheet therefore needs as much memory as the hardest one in the course.

:::table (align := left) +header
* + Resource
  + Minimum
  + Comfortable
* + RAM
  + 16 GB
  + 32 GB
* + Free disk space
  + 20 GB
  + 20 GB
* + Disk
  + SSD
  + NVMe SSD
:::

Most of the RAM requirement comes from memory-mapped library data, which the system can drop and read back from disk, so less memory does not break anything, it only slows everything down by a large margin.

*If your machine is below the minimum, talk to the teachers at the start of the course.* A server with 128 GB of RAM is available and we can give you an account on it.

Run the `git clone` and `lake exe cache get` below at home: `lake exe cache get` downloads several gigabytes, and twenty people doing that at once on one network is slow for all of them.

* Install [*VS Code*](https://code.visualstudio.com/).
* Open *VS Code*, hit the _extensions_ icon (fifth from the top) on the left, and install the _Lean 4 language extension_.
* Install `git`, if you do not have it: open *VS Code*, hit the _git_ icon (third from the top on the left), and follow the instructions.
* The exercises repository. Go to where you want the course materials and run
```
git clone https://github.com/pfaffelh/leancourse_exercises
cd leancourse_exercises
lake exe cache get
code .
```
*VS Code* opens with the course materials. (These notes are generated from a second repository, [pfaffelh/leancourse](https://github.com/pfaffelh/leancourse), which you do not need to clone.)

:::paragraph
Another description of the installation is [here](https://leanprover-community.github.io/get_started.html#regular-install).
:::


After `code .` in the `leancourse_exercises` folder, open `Exercises/0-Logic/a-Propositions.lean`. It works once the orange and red bars disappear and moving the cursor on the left changes the infoview on the right.
Then copy the `Exercises` directory to `MyExercises` and work there. To get updates, run `git pull` in `leancourse_exercises`. `MyExercises` is ignored by git, so an update never overwrites your files.

If the installation gives you trouble, talk to the teachers.

# How these notes are organized
%%%
tag := "notes-layout"
%%%

The notes have six parts.

* *Lean and its type theory*: the natural numbers and reduction, types, terms, typeclasses, propositions as types, dependent types and notation.
* *Mathematics*: sets and types, universes and axioms, well-foundedness, then the areas of *Mathlib* listed above. Pointers into the API, not full formalizations.
* *Appendix*: the glossary of tactics (a longer list is [here](https://github.com/haruhisa-enomoto/mathlib4-all-tactics/blob/main/all-tactics.md)), the structure of a Lean file, navigating *Mathlib*, common pitfalls, and small reference topics such as the diagnostic commands (`#print axioms`, `#find_home`, `#lint`).
* *Projects*: five topics for the individual formalization projects, each with a description, a sketch of an implementation and references.
* *Bibliography*: the works cited throughout, with links.
* *Organization*: what comes when, the short tests, the slides and the recordings.

Tactics and theory are interleaved. You usually meet a tactic in a working example before you read its entry in the glossary, which is meant for looking things up, not for reading in order. The {ref "cheatsheet"}[cheatsheet] lists the tactics needed first.

The exercises carry the course (the `Exercises` folder of the exercises repository, see below). Feedback is immediate: error messages from the elaborator, and the *proof state* in the infoview, which shows what remains to be proved at every cursor position. Start with the first sheet; the sheets explain as they go.

In addition to the sheets, you work on an individual project, mostly self-chosen — an exercise from your first year, or a part of *Mathlib* you want to know; the {ref "projects"}[Projects chapter] has five worked-out suggestions.

Before the first lab session, get Lean running on your own machine.
