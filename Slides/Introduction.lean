import VersoSlides
import Verso.Doc.Concrete
import Mathlib

open VersoSlides

set_option pp.rawOnError true

/-
Deck for the first lecture (week 1, Monday).  It follows the
Introduction of the course notes section by section, so the two can be
shown together: what formalizing means, where things stand in 2026, how
it got there, the landmark projects, and what the course asks of you.
-/

#doc (Slides) "Why formalize?" =>

```css
img.portrait {
  width: 16vh; height: 16vh; object-fit: cover; object-position: 50% 20%;
  border-radius: 50%; margin: 0 0.35rem; vertical-align: middle;
  box-shadow: 0 1px 5px rgba(0, 0, 0, 0.2);
}
/* These two have to outrank `.reveal section p` below, which is why
   they are written out this long. */
.reveal section p.names, .reveal section .names p {
  font-size: 0.45em; color: #52514e; letter-spacing: 0.02em;
  margin: 0.1em 0; }
/* caption under a chart, saying what is plotted */
.reveal section p.caption, .reveal section .caption p {
  font-size: 0.42em; color: #52514e; margin: 0.2em 0 0;
  line-height: 1.35; }
.reveal section img { margin: 0.4rem 0; }
/* reveal's default body size overflows a slide with four or five
   lines under a picture; this is the single knob for that */
.reveal section p { font-size: 0.8em; line-height: 1.32; margin: 0.42em 0; }
/* picture and faces share one horizontal band, directly under the
   heading, so the slide does not grow downwards */
.reveal .r-hstack { align-items: center; justify-content: center;
                    gap: 1.6rem; margin-bottom: 0.3rem; }
.reveal .r-hstack > * { margin: 0; }
/* a portrait keeps its name directly underneath, inside the band */
.reveal .r-hstack .r-vstack { gap: 0; }
.reveal .r-vstack > * { margin: 0; }
.reveal section img.logo { height: 9vh; width: auto; margin: 0 1.2rem; }
/* the six goals, copied from the notes: six items only fit at this size */
.reveal section .goals li { font-size: 0.56em; line-height: 1.3;
                            margin: 0.35em 0; text-align: left; }
.reveal section .goals ul { width: 92%; margin: 0.2em auto; }
/* a comparison table has to leave room for the lines under it */
.reveal section table { font-size: 0.62em; margin: 0.2em auto 0.4em; }
.reveal section table th,
.reveal section table td { padding: 0.18em 0.9em; }
```

# Why formalize?

Interactive theorem proving with Lean -- first lecture.

:::notes
Title slide. The question in the heading is the one the next twenty
minutes answer.
:::

# What formalizing means

Write the proof in a language precise enough for a machine to check every step.

:::fragment fadeUp
*Autoformalizing* runs the other way -- informal mathematics in, formal text out.
:::

:::notes
That is the definition. The machine does not *find* the proof; it reads
yours and checks it, and anything left out is refused.

Both directions end in the same place: a text the kernel accepts. The
program that writes a proof may be unreliable in any way it likes; the
program that checks it is small and fixed. That asymmetry is why any of
this works, and it comes back later as the de Bruijn criterion.

This course is about the first direction. They write the proofs.
:::

# 2026

:::hstack
{image "../static/figures/logos/claude.png" (class := "logo")}[Claude] {image "../static/figures/logos/chatgpt.png" (class := "logo")}[ChatGPT]
:::

:::fragment fadeUp
*Feb* -- sphere packing, dimension 8: a machine finishes it in five days.
:::

:::fragment fadeUp
*4 Sep* -- Fermat's Last Theorem, checked. 11 days, 13 M lines of Lean.
:::

:::fragment fadeUp
*8 Sep* -- Navier-Stokes with a force: a singularity in finite time.
:::

:::fragment fadeUp
*6 Oct* -- 719 manuscripts, 42 % with a Lean proof.
:::

:::notes
FLT: Anthropic, Claude, building on Mathlib, following a simplified
Wiles. Buzzard confirmed it assumes nothing but the axioms.

Navier-Stokes: the *forced* equation. Not the Millennium problem.
The prize is unclaimed. Say this plainly.

February first, and it is the cleanest case: the statement was
settled mathematics, only the formalizing was left. The autoformalizer
is Gauss, from Math Inc.; the human project it joined had been running
since 2024.

One day after that catalogue, three of its manuscripts were withdrawn
over a sign error, and fourteen more were revised. None of the
withdrawn ones had a Lean proof. Say it; do not put it on the slide.

Machines now produce mathematics faster than mathematicians can
referee it, and the only check that keeps up is a formal one. Do not
oversell it -- the next slide takes it back a step.
:::

# But be precise

A Lean proof certifies that *a formal statement* follows from the axioms.

:::fragment fadeUp
Whether that statement is the theorem in the paper is a *human* question.
:::

:::fragment highlightBlue
Reading a formal statement and judging what it says is most of what
this course teaches.
:::

:::notes
OpenAI's repository documents, per paper, which checks cover a main
theorem and which only a supporting result.
:::

# Where people are going

{image "../static/figures/itp_github_repos_per_million.png" (height := "40vh")}[New GitHub repositories per quarter for Lean, Coq/Rocq and Isabelle, 2018 to 2026]

:::class "caption"
New GitHub repositories per quarter for the three large proof
assistants, counted per million new repositories overall.
:::

:::notes
Per million, because GitHub itself grew steeply in 2026. One
distortion is left in: the Justin Sun Prize pays only against a
machine-verified proof, and about a fifth of September's new Lean
repositories carry a prize identifier.

Until about 2023 the three were comparable, and Coq was the larger.

Not evidence that Lean is better. Isabelle's automation is still
ahead in places; Rocq has decades of verified software behind it.
Evidence about where people are going.
:::

# Papers checked in Lean

{image "../static/figures/arxiv_lean_formalized_share.png" (height := "40vh")}[Share of arXiv mathematics papers with a Lean-checked result during 2026, per 100 submissions]

:::class "caption"
Papers on the mathematics arXiv whose results are checked in Lean,
per 100 submissions, by week of submission in 2026.
:::

:::fragment highlightBlue
The denominator doubled too: about 1 000 submissions a week in January, about 2 500 in October.
:::

:::notes
A share, not a count: a rising count would partly be that growth in
submissions, which is itself worth a sentence.

The last bar is the highest so far: 60 of 2 546 papers in the first
week of October, 2.4 per 100. One week, so not a trend by itself.

Within a few years, reading and writing a formal proof will be
ordinary equipment. This is the answer to "why spend a semester on
this".
:::

# How we got here

:::fragment fadeUp
*1879-1936* -- the mathematics. A proof becomes a finite string, and checking one becomes a decidable question.
:::

:::fragment fadeUp
*1967-1991* -- the first checkers: Automath, Mizar, LCF, HOL, Isabelle, Coq.
:::

:::fragment fadeUp
*1976, 1998, 2013, 2020* -- four episodes that made it urgent.
:::

:::fragment highlightBlue
*2013* -- Lean. The idea is 150 years old; the tool is 13.
:::

:::notes
The order is chronological. First the mathematics, which needed from
Frege to Turing to turn a proof into a finite object a machine can
inspect. Then the machines.

Not chronology for its own sake: each of the four episodes adds a
different reason. What a computer proof is worth, where peer review
stops, whether the author can trust himself, and who is asking for
this now.

If the hour is short, the mathematics block is the part to cut.
:::

# Frege, Peano, Russell

::::::hstack
::::vstack
{image "../static/figures/portraits/frege.jpg" (class := "portrait")}[Gottlob Frege]

:::class "names"
Gottlob Frege
:::
::::

::::vstack
{image "../static/figures/portraits/russell.jpg" (class := "portrait")}[Bertrand Russell]

:::class "names"
Bertrand Russell
:::
::::
::::::

:::fragment fadeUp
*1879* -- Frege makes proofs into objects you can calculate with.
:::

:::fragment fadeUp
*1889* -- Peano: zero, successor, induction. Still the shape of Lean's `Nat`.
:::

:::fragment fadeUp
*1902* -- Russell's letter: the set of all sets that are not members of themselves.
:::

:::fragment fadeUp
*1910-13* -- *Principia Mathematica* rebuilds. `1 + 1 = 2` arrives in volume two.
:::

:::notes
The mathematics block. Where the `fun` in `fun x => x + 1` comes
from, and why the machine checks instead of searching. No machines in
it yet -- those start six slides on, with Automath.

Frege's *Begriffsschrift*, 1879: the first system in which a proof is
itself an object you can manipulate.

Russell's letter of 1902 breaks it. Whitehead and Russell then spend
*Principia Mathematica* rebuilding, and the proof that `1 + 1 = 2`
comes with the note that "the above proposition is occasionally
useful".

Both repairs are from 1908, and the difference between them is why
this course is about types. Zermelo replaces unrestricted
comprehension by separation, so the paradoxical set is never formed;
`x in x` stays a well-formed formula, and that it is false for every
set is the axiom of foundation, added later and not the repair.
Russell stratifies the grammar, so `x in x` is not a false statement
but no statement at all. Well-formedness is then decidable, which is
exactly what a type checker decides. Mathematics went with Zermelo,
proof assistants with Russell.

Done by hand, formalization is unbearable. For most of a century
little came of it.
:::

# Two repairs, 1908

:::table +colHeaders +rowSeps
*
  * 1908
  * restricts
  * `x ∈ x` is
  * the stratification is
*
  * Zermelo
  * which sets *exist*
  * well-formed, and false
  * the cumulative hierarchy, a *theorem*
*
  * Russell
  * what may be *said*
  * no statement at all
  * the type hierarchy, a *rule*
:::

:::fragment highlightBlue
Mathematics went with Zermelo, proof assistants with Russell.
:::

:::notes
The whole reason this course is about types.

Zermelo replaces unrestricted comprehension by separation, so the
paradoxical set is never formed. The language is untouched: `x in x`
stays a well-formed formula, and that it is false for every set is
the axiom of foundation, added by von Neumann in 1925 and Zermelo in
1930 -- later, and not the repair.

Russell stratifies the grammar. `x in x` is not a false statement but
no statement at all, so well-formedness is a question about syntax
and is decidable. That is what a type checker decides, and it is why
Lean has `Type 0 : Type 1 : ...` and no type of all types.

Both hierarchies exist; the difference is who enforces them. In set
theory the cumulative hierarchy is a theorem about which sets there
are, and you may write the bad expression and then prove it denotes
nothing. In type theory you do not get that far.
:::

# Hilbert's programme

::::vstack
{image "../static/figures/portraits/hilbert.jpg" (class := "portrait")}[David Hilbert]

:::class "names"
David Hilbert
:::
::::

:::fragment fadeUp
Fix the language, fix the rules. A proof becomes a finite string, and checking it is a question about symbols.
:::

:::fragment fadeUp
*Consistent?* -- no contradiction follows from the axioms.
:::

:::fragment fadeUp
*Complete?* -- for every statement, it or its negation follows.
:::

:::fragment fadeUp
*Decidable?* -- a procedure settles which of the two.
:::

:::fragment highlightBlue
Hilbert wants all three.
:::

:::notes
Hilbert pushes this from a lecture of 1917, *Axiomatisches Denken*, on
through the 1920s. The conviction is older: Paris 1900, "denn in der
Mathematik gibt es kein Ignorabimus" -- no question we are condemned
never to settle.

The formalization half is exactly what a proof assistant does. A proof
is a finite object, and whether it follows the rules can be decided
without knowing what the symbols mean.

The consistency proof was to use finitary means only -- no appeal to
the infinite objects whose consistency was in question.
:::

# Gödel, 1929 and 1931

::::vstack
{image "../static/figures/portraits/godel.jpg" (class := "portrait")}[Kurt Gödel]

:::class "names"
Kurt Gödel
:::
::::

:::table +colHeaders +rowSeps
*
  * Gödel
  * about
  * result
*
  * 1929
  * first-order logic
  * complete: valid in every model is derivable
*
  * 1931
  * any theory containing arithmetic
  * incomplete: some truth about ℕ is neither proved nor refuted
:::

:::fragment fadeUp
Cantor's diagonal argument, moved from the reals to proofs.
:::

:::notes
Two theorems, opposite directions, by the same person.

1929, his thesis: first-order logic is complete. Logic itself is not
the obstacle. This is what makes proof search terminate when a proof
exists -- row two on the table in a moment.

*First-order* means the quantifiers range over the elements of a
domain, never over its subsets. "For all x, y in the group" is
first-order; "every bounded set of reals has a supremum" is not.
Lean is not first-order -- it quantifies over types and over
propositions -- so this theorem does not apply to Lean.

Watch the word *complete*, which does two jobs. A *logic* is complete
when everything valid is derivable; a *theory* is complete when it
decides every statement. 1929 is the first, Hilbert's second question
and 1931 are the second. No conflict: the sentence of 1931 is true of
the naturals but false in other models of the axioms, so it is not
valid, and 1929 says nothing about it.

1931: the incompleteness theorems. Any consistent system containing
arithmetic, with axioms a machine can list, misses true statements
about the naturals, and cannot prove its own consistency. The
programme fails; the formalization stays.

Gödel's proof is itself the first serious piece of formalization: he
encodes formulas and proofs as numbers and computes with them. Proofs
as data.
:::

# 1936: the Entscheidungsproblem

::::::hstack
::::vstack
{image "../static/figures/portraits/placeholder_church.png" (class := "portrait")}[Alonzo Church]

:::class "names"
Alonzo Church
:::
::::

::::vstack
{image "../static/figures/portraits/turing.jpg" (class := "portrait")}[Alan Turing]

:::class "names"
Alan Turing
:::
::::
::::::

:::fragment fadeUp
*1928* -- Hilbert and Ackermann: is there a procedure deciding whether a formula is provable? The *Entscheidungsproblem*.
:::

:::fragment fadeUp
*1936* -- Church and Turing, independently: there is none.
:::

:::fragment fadeUp
First they had to say what a procedure is. Turing: a tape, a head, a finite table of instructions. Church: the $`\lambda`-calculus.
:::

:::notes
Hilbert and Ackermann, *Grundzüge der theoretischen Logik*, 1928.

Church's paper was submitted in April 1936, Turing's a few months
later. Neither knew of the other at the start. Turing went to
Princeton the year after and took his doctorate under Church.

Turing's machine is not a design. Nothing in the paper says how one
would be built; it exists to be reasoned about.

The two models compute the same functions -- that is a theorem, in an
appendix to Turing's paper. That either of them is what "computable"
means is not a theorem. That is the Church-Turing thesis, a claim
about the word.

There is no photograph of Church that is free to use -- the silhouette
is deliberate, like the others in these slides.
:::

# The lambda calculus

:::fragment fadeUp
A notation for functions, and nothing else.
:::

:::fragment fadeUp
$`\lambda x.\, x + 1` is the function adding one. The only rule is substitution: $`(\lambda x.\, x + 1)\, 3` becomes $`3 + 1`.
:::

:::fragment fadeUp
Numbers, pairs and recursion are not built in. They are written as $`\lambda`-terms, and that is enough for everything Turing's machines compute.
:::

:::fragment fadeUp
Lean is this notation with types on top:
:::

```lean -panel -stretch
example : (fun x : Nat => x + 1) 3 = 3 + 1 := rfl
```

:::notes
This is ninety years old and you will type it all semester. `fun x =>`
is `λx.`, and Lean accepts `λ` too.

The kernel computes by substituting, which is the rule above and
nothing more.

Curry-Howard, the step from functions to proofs: a proposition is a
type, a proof is a term of that type, and checking a proof is
type-checking a program. Curry saw it for implication in the 1930s; de
Bruijn, Howard and Läuchli extended it to the quantifiers in the
1960s. It is why `theorem` and `def` are the same thing in Lean.
:::

# Checking is not finding

::::table +colHeaders +rowSeps
*
  * Is there a procedure that
  * confirms it when true
  * refutes it when false
  * verdict
*
  * *this text proves the statement*
  * yes, always stops
  * yes, always stops
  * decidable
*
  * *the statement has some proof*
  * yes, whenever a proof exists
  * no such procedure
  * semi-decidable only
::::

:::fragment highlightBlue
You prove. The machine checks. That split is a theorem, not a gap in today's software.
:::

:::notes
Row one is the kernel, and the whole trust of the system sits there.

Row two is the automation: `exact?`, `apply?`, `grind`. Proofs can be
enumerated, so a search terminates when there is something to find. If
there is nothing, it runs forever -- hence the time limit on every one
of these tactics.

Row three is the Entscheidungsproblem itself.

Rows two and three look contradictory and are not. They are the same
set of statements. Semi-decidable: every yes is eventually found.
Undecidable: the noes are not -- nothing reliably reports that a
statement has no proof. The gap is one-sided, and it is exactly what
you see when `grind` hangs. It cannot say there is nothing there,
only that it has not found anything yet.

This is the answer to "why doesn't the computer just do it".
:::

# 1967: Automath

::::vstack
{image "../static/figures/portraits/debruijn.jpg" (class := "portrait")}[Nicolaas Govert de Bruijn]

:::class "names"
Nicolaas Govert de Bruijn
:::
::::

:::fragment fadeUp
*Automath* -- a typed $`\lambda`-calculus with dependent types, not set theory. The first machine-checked proofs.
:::

:::fragment fadeUp
*1977* -- Landau's *Grundlagen der Analysis* through it, end to end.
:::

:::fragment fadeUp
Then *Mizar* 1973, *LCF* 1975, *HOL*, *Isabelle* 1986, *Coq* 1989.
:::

:::fragment highlightBlue
Everything before this slide is mathematics. From here on there are machines.
:::

:::notes
Say what he turned away from. Since 1954 the attempt had been to make
the machine *find* proofs: Davis on the JOHNNIAC, the Logic Theory
Machine of 1956, Wang 1959, Robinson's resolution in 1965. It works
for logic calculi and not for mathematics. De Bruijn retreats to the
cheap question -- the human proves, the machine checks. That is the
split between *automated* and *interactive* theorem proving, and the
title of this course sits on one side of it.

De Bruijn starts Automath at Eindhoven in 1967 and publishes in 1968.
He arrives at the Curry-Howard correspondence himself, not knowing
Howard's work, and is the first to use it in a running system. Van
Benthem Jutting's 1977 thesis pushes Landau's book through it: the
first mathematics book verified end to end.

Two architectures come out of the next twenty years. LCF, Milner 1972
and 1975: `thm` is an abstract data type and only the inference rules
can produce one, so nothing above the kernel needs trusting; ML was
invented to write it. Automath's line instead writes down a proof
term, which a small separate checker reads afterwards -- the de Bruijn
criterion. Lean is in that line. A Lean proof is a term, and the
kernel rechecks it whatever tactic produced it.

:::

# 1976: the four colour theorem

::::::hstack
{image "../static/figures/four_colour.png" (height := "22vh")}[A map of thirty-four regions coloured with four colours]

::::vstack
{image "../static/figures/portraits/placeholder_gonthier.png" (class := "portrait")}[Georges Gonthier]

:::class "names"
Georges Gonthier
:::
::::
::::::

Appel and Haken reduce the problem to a list of configurations, and an ordinary program checks it -- no proof assistant.

:::fragment fadeUp
*No human has ever read that part.*
:::

:::fragment highlightBlue
2005: Gonthier redoes all of it in *Coq*, case analysis included.
:::

:::notes
Two decades of argument about whether this counted as a proof.
Gonthier did not settle it; he made it unnecessary.

The 1976 program was Fortran and assembler on an IBM 370: a program
you had to trust. Coq is the opposite arrangement -- a kernel of a few
thousand lines, and everything else checked against it.
:::

# 1998: the Kepler conjecture

::::::hstack
{image "../static/figures/kepler_packing.png" (height := "22vh")}[A pyramid of equal spheres, the face-centred cubic packing]

::::vstack
{image "../static/figures/portraits/hales.jpg" (class := "portrait")}[Thomas Hales]

:::class "names"
Thomas Hales
:::
::::
::::::

Hales announces a proof of Kepler's conjecture of 1611. Twelve referees, four years.

:::fragment fadeUp
Verdict: *ninety-nine percent certain* -- and no better was possible. The *Annals* published it with the caveat attached.
:::

:::fragment highlightBlue
Hales started Flyspeck. Complete formal proof in HOL Light and Isabelle, 2014.
:::

:::notes
Not about computers. Peer review met a proof it could not certify,
and more effort would not have helped.

Sixteen years from announcement to a proof anyone could check.
:::

# 2013: Voevodsky

::::vstack
{image "../static/figures/portraits/voevodsky.jpg" (class := "portrait")}[Vladimir Voevodsky]

:::class "names"
Vladimir Voevodsky
:::
::::

*1989* -- Voevodsky and Kapranov identify $`\infty`-groupoids with homotopy types.

:::fragment fadeUp
*Oct 1998* -- Simpson argues that it cannot be true, but cannot say *which step*.
:::

:::fragment fadeUp
*Autumn 2013* -- Voevodsky accepts it. Fifteen years unused, and unrefuted.
:::

:::fragment highlightBlue
Mathematics runs on *a complex system of mutual trust based on reputations*.
:::

:::notes
Note the dates: the paper is from 1989, but the episode only ends in
2013, which is why it sits here and not before Kepler.

Fifteen years, and not an obscure corner: both authors were well
known, and Voevodsky received the Fields Medal in between, in 2002. Everyone makes mistakes. What matters here is how long it took
to resolve, and why: nobody could point at the faulty step, so it was
unclear who had erred, and nobody challenged them.

The quoted line is Voevodsky's own, from his 2014 IAS lecture.

Second story, same lesson: a mistake in a lemma of his own from 1992
stayed in print until someone checking his lectures step by step found
it in 1999. Several seminars had read the paper by then.

His conclusion: a hard technical argument by a trusted author is
*hardly ever checked in detail*.

He then looked for a proof assistant, found none he could use, and
built the foundations for one: univalent foundations, the IAS special
year 2012-13, the HoTT book. In Coq, not Lean, and not the foundations
Mathlib uses. We take the diagnosis, not the cure. He died in 2017.
:::

# 2020: the Liquid Tensor Experiment

::::::hstack
::::vstack
{image "../static/figures/portraits/scholze.jpg" (class := "portrait")}[Peter Scholze]

:::class "names"
Peter Scholze
:::
::::

::::vstack
{image "../static/figures/portraits/placeholder_commelin.png" (class := "portrait")}[Johan Commelin]

:::class "names"
Johan Commelin
:::
::::
::::::

Scholze posts a challenge on Buzzard's blog: a theorem in condensed mathematics he is not certain of.

:::fragment fadeUp
Liquid Tensor Experiment, led by Commelin. Finished July 2022.
:::

:::fragment highlightBlue
The request came from a working mathematician, not from logicians. That is what had changed.
:::

:::notes
Buzzard's ICM plenary in 2022 is a fair marker for the moment this
stopped being a curiosity.

Not combinatorics with a thousand cases, either -- condensed
mathematics, at the research frontier.
:::

# 2013: Lean

::::vstack
{image "../static/figures/portraits/demoura.jpg" (class := "portrait")}[Leonardo de Moura]

:::class "names"
Leonardo de Moura
:::
::::

:::fragment fadeUp
*2013* -- Leonardo de Moura starts Lean at Microsoft Research.
:::

:::fragment fadeUp
*2021* -- Lean 4, a redesign rather than a new version.
:::

:::fragment fadeUp
Foundation: the Calculus of Inductive Constructions, the Automath line. A proof is a term, and the kernel rechecks it.
:::

:::notes
Lean 1 to 3 were research prototypes; Lean 4 is the one that stuck,
and it is written in itself.

Kevin Buzzard has argued for Lean among mathematicians since 2018.
That is roughly when Mathlib started to look like a library of real
mathematics rather than a collection of exercises.

De Moura is still chief architect, now at the Lean FRO -- next slide.
:::

# Lean today

:::fragment fadeUp
A new Lean every month. `v4.34.0` on 14 September 2026, `v4.35.0` on 12 October.
:::

:::fragment fadeUp
Nothing updates by itself. `lean-toolchain` names one version, `elan` fetches it, `lake` builds against it.
:::

:::fragment highlightBlue
This course is pinned to `v4.34.0` all semester.
:::

:::fragment fadeUp
[*Lean FRO*](https://lean-lang.org/fro/) -- a non-profit since July 2023, twenty-one people, living on donations.
:::

:::notes
Monthly releases, with a release candidate about four weeks ahead.
Patch releases in between.

The pin is why the notes and their machines agree. Tell them not to
run `elan update` and wonder why the exercises stop compiling.

Lean FRO: founded July 2023 under Convergent Research. De Moura chief
architect, Sebastian Ullrich head of engineering. Funders: Simons
Foundation International, Sloan, Richard Merkin, Amazon, and five
million dollars from Alex Gerko in July 2025. No vendor, and no longer
a spare-time project.
:::

# Mathlib

One library, one repository, one version. Everything in this course imports it.

:::fragment fadeUp
2.33 million lines, about 189 000 theorems, 1 031 contributors. 27 commits a day.
:::

:::fragment fadeUp
No stable releases. *Mathlib* follows Lean, your project follows *Mathlib*.
:::

:::fragment fadeUp
[*The Mathlib Initiative*](https://mathlib-initiative.org/) -- since September 2025, maintainers are paid to maintain it.
:::

:::fragment highlightBlue
[The interactive import map](https://leanprover-community.github.io/mathlib4_docs/mathlib.html) -- the whole of *Mathlib* as a graph of its modules.
:::

:::notes
Measured on the pinned version of 15 September 2026: 8 529 files,
2.33 M lines, ~189 000 theorems, ~64 000 definitions, 1 031
contributors, 34 768 commits. 820 commits in the preceding thirty
days. The library changes while they use it.

`lake exe cache get` fetches what CI already compiled. Building from
source takes hours. Say this before the lab session.

Mathlib Initiative: a programme of Renaissance Philanthropy, the other
five million of Gerko's gift. Targets: review within a week for nine
of ten pull requests, keep the downstream ecosystem building,
documentation. Johan Commelin, who led the Liquid Tensor Experiment,
works there.

Open the import map live: one connected library, not a pile of
packages. Point at a node, follow an edge, show how analysis sits on
order sits on algebra.
:::

# Perfectoid spaces, 2019

::::::hstack
::::vstack
{image "../static/figures/portraits/buzzard.jpg" (class := "portrait")}[Kevin Buzzard]

:::class "names"
Kevin Buzzard
:::
::::

::::vstack
{image "../static/figures/portraits/placeholder_commelin.png" (class := "portrait")}[Johan Commelin]

:::class "names"
Johan Commelin
:::
::::

::::vstack
{image "../static/figures/portraits/placeholder_massot.png" (class := "portrait")}[Patrick Massot]

:::class "names"
Patrick Massot
:::
::::
::::::

*The problem:* could an object as complicated as Scholze's perfectoid space be *stated* at all in a proof assistant?

:::fragment highlightBlue
They formalized a *definition*, not a theorem. Stating is a different problem from proving.
:::

:::notes
Scholze's perfectoid spaces, 2012.

Lean's reputation among mathematicians dates from this project.
:::

# Sphere eversion, 2022

::::::hstack
::::vstack
{image "../static/figures/portraits/placeholder_massot.png" (class := "portrait")}[Patrick Massot]

:::class "names"
Patrick Massot
:::
::::

::::vstack
{image "../static/figures/portraits/placeholder_vandoorn.png" (class := "portrait")}[Floris van Doorn]

:::class "names"
Floris van Doorn
:::
::::

::::vstack
{image "../static/figures/portraits/placeholder_nash.png" (class := "portrait")}[Oliver Nash]

:::class "names"
Oliver Nash
:::
::::
::::::

*The problem:* Mathlib had no differential geometry, and Gromov's h-principle needs it.

:::fragment highlightBlue
So they built the API first and proved the theorem afterwards. That order is the ordinary shape of the work.
:::

:::notes
A sphere can be turned inside out without tearing or creasing. In the
plane the turning number blocks the analogue: $`+1` cannot become
$`-1`. In three dimensions that obstruction is gone.

This is why Mathlib matters more than any single theorem in it.
:::

# Freiman-Ruzsa, 2023

::::::hstack
::::vstack
{image "../static/figures/portraits/gowers.jpg" (class := "portrait")}[Timothy Gowers]

:::class "names"
Timothy Gowers
:::
::::

::::vstack
{image "../static/figures/portraits/green.jpg" (class := "portrait")}[Ben Green]

:::class "names"
Ben Green
:::
::::

::::vstack
{image "../static/figures/portraits/tao.jpg" (class := "portrait")}[Terence Tao]

:::class "names"
Terence Tao
:::
::::

::::vstack
{image "../static/figures/portraits/placeholder_manners.png" (class := "portrait")}[Freddie Manners]

:::class "names"
Freddie Manners
:::
::::
::::::

*The problem:* a formalization took one team years, so it always came long after the paper.

:::fragment highlightBlue
A *blueprint* cuts the work into pieces with stated interfaces. Strangers in parallel, three weeks, before refereeing.
:::

:::notes
A set whose sumset is barely larger than itself must be structured.

The method carried further than the theorem: this is the step between
"LTE, two years" and "Fermat, eleven days".
:::

# Equational Theories, 2024-25

*The problem:* 22 028 942 implications between 4 694 laws on magmas. Not deep -- but beyond any human team.

```lean -panel -stretch
abbrev Equation3 (a : Type) [Mul a] :=
  ∀ x : a, x = x * x

abbrev Equation4 (a : Type) [Mul a] :=
  ∀ x y : a, x = x * y

-- Equation 4 implies Equation 3: take y := x.
example (a : Type) [Mul a] (h : Equation4 a) :
    Equation3 a :=
  fun x => h x x
```

:::notes
Led by Terence Tao. All implications settled, with new constructions
found on the way.

That is one entry of twenty-two million. Proving an implication can be
a single substitution; refuting one means building a magma, and the
machine checks that too, by `decide`.
:::

# Sphere packing, dim. 8 and 24

::::vstack
{image "../static/figures/portraits/viazovska.jpg" (class := "portrait")}[Maryna Viazovska]

:::class "names"
Maryna Viazovska
:::
::::

*The problem:* the mathematics was finished in 2016, and formalizing it still took a human project two years.

:::fragment highlightBlue
In Lean, on *Mathlib*. An autoformalizer closed dimension 8 in five days, February 2026.
:::

:::notes
Viazovska 2016, Fields Medal 2022. The packing is the E8 lattice.

Same system as everything else in this lecture: Lean, building on
Mathlib. The human project started in 2024.

This closes the thread that opened with Kepler, four hundred years
earlier -- and it is the February entry from the 2026 slide.
:::

# Three systems

:::table +colHeaders +rowSeps
*
  * System
  * Logic
  * Library
*
  * *Lean 4*
  * dependent types
  * one: *Mathlib*
*
  * *Rocq* (Coq until 2025)
  * dependent types
  * many packages
*
  * *Isabelle/HOL*
  * simple type theory
  * the *AFP*
:::

:::fragment fadeUp
Only Isabelle has no dependent types. Its automation is the strongest of the three.
:::

:::fragment highlightBlue
We use Lean because *Mathlib* exists.
:::

:::notes
A proof is a term (Lean, Rocq, Agda), a derivation in a calculus
(Isabelle, HOL Light), or a text in set theory (Mizar, Metamath).
Three answers to one question.

All of them share the de Bruijn criterion: a tiny kernel you have to
trust, and arbitrarily unreliable automation above it. That is why
`grind` is allowed to be as clever as it likes.
:::

# Goals

The course is for mathematics students.

:::class "goals"
* *Interactive theorem proving.* A small kernel checks every logical step of a proof, and the editor reports what remains to be proved as you write. This is not the older use of computers in mathematics, which was to work through many cases.
* *Mathematical content.* The mathematics in the first half is deliberately easy, because explaining a proof to a computer requires understanding it first, and a proof of more than a few lines has to be planned so that the commands -- *tactics* -- fit together. The second half goes deeper into the mathematics.
* *Functional programming.* Inductive types, structures, typeclasses and monads, needed both to use Lean and to read *Mathlib*. These are spread across the Lean and Mathematics parts rather than collected in one chapter.
* *Type theory.* Lean rests on dependent type theory: the Curry-Howard correspondence, dependent types, the universe hierarchy, and Lean's axioms.
* *Mathematics in Mathlib.* How the library organizes order theory, the algebraic hierarchy, filters (a single framework for limits), topology, measure theory and discrete probability. Textbooks rarely treat these from the point of view of formalization.
* *Proof engineering.* Automation tactics, searching *Mathlib*, and the common pitfalls of a large formal library.
:::

:::notes
Word for word the goals from the notes, so nobody has to reconcile two
versions. Read the first three out, point at the last three.

The exercises carry the course. The sheets cover the first half of the
semester; in the second half they work on a project, mostly
self-chosen.
:::

# Where to start

:::fragment fadeUp
[Natural Number Game](https://adam.math.hhu.de/#/g/leanprover-community/nng4) -- in the browser, nothing to install. Start here.
:::

:::fragment fadeUp
[Formalising Mathematics](https://b-mehta.github.io/formalising-mathematics-notes/) -- Bhavik Mehta, after Kevin Buzzard.
:::

:::fragment fadeUp
[Mathematics in Lean](https://leanprover-community.github.io/mathematics_in_lean/) -- Avigad and Massot. The closest thing to an official course.
:::

:::notes
The Natural Number Game runs in a browser and takes an evening. If
they do one thing before Wednesday, that is it.

The other two are references for the semester, not homework.
:::

# What your machine needs

Every sheet begins with `import Mathlib`, so a two-line sheet needs as much memory as the hardest one.

:::table +colHeaders +rowSeps
*
  * Resource
  * Minimum
  * Comfortable
*
  * RAM
  * 16 GB
  * 32 GB
*
  * Free disk
  * 20 GB
  * 20 GB
*
  * Disk
  * SSD
  * NVMe SSD
:::

:::fragment highlightBlue
Below the minimum? Talk to us -- there is a server with 128 GB.
:::

:::notes
Compiling one sheet peaks at about 6.6 GB resident; the language
server sits at roughly 9 GB with one file open. Most of that is
memory-mapped library data the system can drop and read back, so less
memory slows everything down rather than breaking it. On a mechanical
hard disk you cannot work at all.
:::

# Wednesday

:::fitText
Bring a laptop. With administrator rights.
:::

:::fragment fadeUp
Follow the [installation instructions](https://pfaffelh.github.io/leancourse/Introduction/#practical) in the course notes beforehand.
:::

:::fragment highlightBlue
Then run `lake exe cache get` *before* you come.
:::

:::notes
Installation session. VS Code, the Lean extension, git clone,
`lake exe cache get`. Ask them to try it at home first, so that
Wednesday is for the ones it did not work for.

Say the last point twice. `lake exe cache get` downloads the compiled
Mathlib; without it every machine in the room compiles Mathlib from
source at once, which takes hours and kills the session.
:::
