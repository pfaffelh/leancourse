import VersoSlides
import Verso.Doc.Concrete
import Mathlib

open VersoSlides

set_option pp.rawOnError true

/-
Deck for the first lecture (week 1, Monday).  It follows the opening
chapter of the course notes section by section, so the two can be shown
together: what formalizing means, where things stand in 2026, how it got
there, and the landmark projects.  Same claims, same figures.
-/

#doc (Slides) "Why formalize?" =>

```css
img.portrait {
  width: 17vh; height: 17vh; object-fit: cover; object-position: 50% 20%;
  border-radius: 50%; margin: 0 0.35rem; vertical-align: middle;
  box-shadow: 0 1px 5px rgba(0, 0, 0, 0.2);
}
.names { font-size: 0.45em; color: #52514e; letter-spacing: 0.02em;
         margin-top: 0.1em; }
.reveal section img { margin: 0.4rem 0; }
/* picture and faces share one horizontal band, directly under the
   heading, so the slide does not grow downwards */
.reveal .r-hstack { align-items: center; justify-content: center;
                    gap: 1.6rem; margin-bottom: 0.3rem; }
.reveal .r-hstack > * { margin: 0; }
.reveal section img.logo { height: 11vh; width: auto; margin: 0 1.2rem; }
/* a comparison table has to leave room for the lines under it */
.reveal section table { font-size: 0.62em; margin: 0.2em auto 0.4em; }
.reveal section table th,
.reveal section table td { padding: 0.18em 0.9em; }
```

# Why formalize?

:::fitText
A proof *found* by computer is not a proof *checked* by computer.
:::

:::notes
The whole lecture in one line. Come back to it at the end.
:::

# What formalizing means

Write the proof in a language precise enough for a machine to check every step.

:::fragment fadeUp
The machine does not *find* the proof. It reads yours and checks it.
:::

:::fragment highlightBlue
Anything you leave out is refused.
:::

:::notes
That is the definition. The rest of the lecture is why it matters.
:::

# Two things it is not

:::fragment fadeUp
*Finding* a proof is not *checking* one. 1976: a computer checked the case list, nothing checked the argument around it.
:::

:::fragment fadeUp
*Autoformalizing* runs the other way -- informal mathematics in, formal text out.
:::

:::fragment highlightBlue
Both end in the same place: a text the kernel accepts.
:::

:::notes
Sphere packing in dimension 8 is both at once. A human formalization
project started in 2024; a machine finished it in five days in
February 2026.

The program that writes a proof may be unreliable in any way it likes.
The program that checks it is small and fixed. That asymmetry is why
any of this works, and it comes back later as the de Bruijn criterion.

This course is about the first direction. They write the proofs.
:::

# 2026

:::hstack
{image "../static/figures/logos/claude.png" (class := "logo")}[Claude] {image "../static/figures/logos/chatgpt.png" (class := "logo")}[ChatGPT]
:::

:::fragment fadeUp
*Feb* -- sphere packing in dimension 8, finished by a machine in five days.
:::

:::fragment fadeUp
*4 Sep* -- Fermat's Last Theorem, computer-checked. 11 days, 13 million lines of Lean.
:::

:::fragment fadeUp
*8 Sep* -- Navier-Stokes with a smooth force: finite-time singularity, formalized.
:::

:::fragment fadeUp
*6 Oct* -- 719 manuscripts, 372 families, about 42 % with a Lean proof.
:::

:::fragment fadeUp
*7 Oct* -- three of them withdrawn. A sign error.
:::

:::notes
FLT: Anthropic, Claude, building on Mathlib, following a simplified
Wiles. Buzzard confirmed it assumes nothing but the axioms.

Navier-Stokes: the *forced* equation. Not the Millennium problem.
The prize is unclaimed. Say this plainly.

February first, and it is the cleanest case: the statement was
settled mathematics, only the formalizing was left. Everything after
it is harder to judge.

The last two dates belong together -- next slide.
:::

# One day apart

:::fitText
None of the withdrawn papers had a Lean proof.
:::

:::notes
Machines now produce mathematics faster than mathematicians can
referee it. The only check that keeps up is a formal one.

Do not oversell it. The next slide takes it back a step.
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

{image "../static/figures/itp_github_repos_per_million.png"}[New GitHub repositories per quarter for Lean, Coq/Rocq and Isabelle, 2018 to 2026]

:::notes
Until about 2023 the three were comparable, and Coq was the larger.

Not evidence that Lean is better. Isabelle's automation is still
ahead in places; Rocq has decades of verified software behind it.
Evidence about where people are going.
:::

# Papers checked in Lean

{image "../static/figures/arxiv_lean_formalized_weekly.png"}[Weekly count of arXiv papers with Lean-checked results during 2026]

:::fragment highlightBlue
January: a handful a week. September: around forty.
:::

:::notes
Within a few years, reading and writing a formal proof will be
ordinary equipment. This is the answer to "why spend a semester on
this".
:::

# How it got here

:::fragment fadeUp
- 1976 -- the four colour theorem
:::

:::fragment fadeUp
- 1998 -- the Kepler conjecture
:::

:::fragment fadeUp
- 2013 -- Voevodsky concedes
:::

:::fragment fadeUp
- 2020 -- the Liquid Tensor Experiment
:::

:::notes
Now how it got there, in order.

Not chronology for its own sake: each episode adds a different reason.
What a computer proof is worth, where peer review stops, whether the
author can trust himself, and who is asking for this now.
:::

# The idea is old

{image "../static/figures/portraits/demoura.jpg" (class := "portrait")}[Leonardo de Moura]

:::class "names"
Leonardo de Moura, who started Lean in 2013
:::

:::fragment fadeUp
- 1879 Frege -- proofs become objects
:::

:::fragment fadeUp
- 1902 Russell's letter -- the system is inconsistent
:::

:::fragment fadeUp
- *Principia*: `1 + 1 = 2`, with the note *"the above proposition is occasionally useful"*
:::

:::fragment fadeUp
- 1967 Automath, 1977 Landau's *Grundlagen* by machine
:::

:::fragment highlightBlue
The idea is 150 years old. The tool is 20.
:::


:::notes
Lean itself: de Moura, Microsoft Research, 2013. Lean 4 in 2021.
Lean FRO, about twenty people. Buzzard arguing for it since 2018.
:::

# 1976: four colours

:::hstack
{image "../static/figures/four_colour.png" (height := "26vh")}[A map of thirty-four regions coloured with four colours]

{image "../static/figures/portraits/placeholder_gonthier.png" (class := "portrait")}[Georges Gonthier]
:::

:::class "names"
Georges Gonthier
:::

Appel and Haken reduce the problem to a long list of configurations.

A computer checks the list.

:::fragment fadeUp
*No human has ever read that part.*
:::

:::fragment highlightBlue
2005: Gonthier formalizes all of it in Coq -- case analysis included.
:::


:::notes
Two decades of argument about whether this counted as a proof.
Gonthier did not settle it; he made it unnecessary.
:::

# 1998: stacking oranges

:::hstack
{image "../static/figures/kepler_packing.png" (height := "27vh")}[A pyramid of equal spheres, the face-centred cubic packing]

{image "../static/figures/portraits/hales.jpg" (class := "portrait")}[Thomas Hales]
:::

:::class "names"
Thomas Hales
:::

:::notes
Kepler, 1611. Hales announces a proof in 1998.
:::

# The referees gave up

Twelve referees. Four years.

:::fragment fadeUp
Verdict: *ninety-nine percent certain* -- and no better was possible.
:::

:::fragment fadeUp
The *Annals* published it with the caveat attached.
:::

:::fragment highlightBlue
Hales started Flyspeck. Complete formal proof, 2014.
:::

:::notes
Not about computers. Peer review met a proof it could not certify,
and more effort would not have helped.
:::

# 2013: the author concedes

{image "../static/figures/portraits/voevodsky.jpg" (class := "portrait")}[Vladimir Voevodsky]

:::class "names"
Vladimir Voevodsky
:::

*1989* -- Voevodsky and Kapranov identify $`\infty`-groupoids with homotopy types.

:::fragment fadeUp
*Oct 1998* -- Simpson posts an argument that it cannot be true.
:::

:::fragment highlightBlue
*Autumn 2013* -- Voevodsky accepts that Simpson was right.
:::


:::notes
Note the dates: the paper is from 1989, but the episode only ends in
2013, which is why it sits here and not before Kepler.

Fifteen years, and not an obscure corner: both authors were well
known, and Voevodsky received the Fields Medal in between, in 2002.

Everyone makes mistakes. What matters here is how long it took to
resolve, and why.
:::

# Why it took fifteen years

Simpson had a counterexample -- but could not say *which step* was wrong.

:::fragment fadeUp
So it was unclear who had erred. Nobody challenged them.
:::

:::fragment highlightBlue
Mathematics runs on *a complex system of mutual trust based on reputations*.
:::

:::notes
Voevodsky's own words, from his 2014 IAS lecture.

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

# 2020: a Fields medallist is unsure

:::hstack
{image "../static/figures/cantor_profinite.png" (height := "21vh")}[Seven stages of the middle-thirds construction]

{image "../static/figures/portraits/scholze.jpg" (class := "portrait")}[Peter Scholze] {image "../static/figures/portraits/placeholder_commelin.png" (class := "portrait")}[Johan Commelin]
:::

:::class "names"
Peter Scholze, Johan Commelin
:::

Scholze posts a challenge on Buzzard's blog.

He is not certain of his own theorem.

:::fragment fadeUp
Liquid Tensor Experiment, led by Commelin. Finished July 2022.
:::

:::fragment fadeUp
Not combinatorics with a thousand cases -- condensed mathematics.
:::


:::notes
Buzzard's ICM plenary in 2022 is a fair marker for the moment this
stopped being a curiosity.
:::

# In between

:::fitText
Each one showed that something new was possible.
:::

:::notes
Five projects between Flyspeck and 2026. The course material is built
out of the libraries they left behind.
:::

# Perfectoid spaces, 2019

:::hstack
{image "../static/figures/padic_tree.png" (height := "21vh")}[The 3-adic integers as a ternary tree]

{image "../static/figures/portraits/buzzard.jpg" (class := "portrait")}[Kevin Buzzard] {image "../static/figures/portraits/placeholder_commelin.png" (class := "portrait")}[Johan Commelin] {image "../static/figures/portraits/placeholder_massot.png" (class := "portrait")}[Patrick Massot]
:::

:::class "names"
Kevin Buzzard, Johan Commelin, Patrick Massot
:::

:::fragment highlightBlue
They formalized a *definition*, not a theorem.
:::


:::notes
Scholze's perfectoid spaces, 2012. Whether an object of that complexity
could be *stated* at all in a proof assistant was open, and stating is
a different problem from proving.

Lean's reputation among mathematicians dates from this project.
:::

# Sphere eversion, 2022

:::hstack
{image "../static/figures/turning_number.png" (height := "21vh")}[Four closed plane curves with their turning numbers]

{image "../static/figures/portraits/placeholder_massot.png" (class := "portrait")}[Patrick Massot] {image "../static/figures/portraits/placeholder_vandoorn.png" (class := "portrait")}[Floris van Doorn] {image "../static/figures/portraits/placeholder_nash.png" (class := "portrait")}[Oliver Nash]
:::

:::class "names"
Patrick Massot, Floris van Doorn, Oliver Nash
:::

:::fragment fadeUp
In the plane the turning number blocks it: $`+1` cannot become $`-1`.
:::

:::fragment highlightBlue
In three dimensions the obstruction is gone.
:::


:::notes
Gromov's h-principle. Differential topology, not algebra, so the
project built a differential-geometry API first and proved the theorem
afterwards. That order is the ordinary shape of formalization work,
and the reason Mathlib matters more than any single theorem in it.
:::

# Freiman-Ruzsa, 2023

:::hstack
{image "../static/figures/sumset.png" (height := "21vh")}[A set of small doubling beside its sumset]

{image "../static/figures/portraits/gowers.jpg" (class := "portrait")}[Timothy Gowers] {image "../static/figures/portraits/green.jpg" (class := "portrait")}[Ben Green] {image "../static/figures/portraits/tao.jpg" (class := "portrait")}[Terence Tao] {image "../static/figures/portraits/placeholder_manners.png" (class := "portrait")}[Freddie Manners]
:::

:::class "names"
Timothy Gowers, Ben Green, Terence Tao, Freddie Manners
:::

:::fragment fadeUp
Formalized in about three weeks -- *before* the paper was refereed.
:::


:::notes
The method carried further than the theorem. A *blueprint* cuts a
formalization into independent pieces with stated interfaces, so
volunteers can work in parallel without talking to each other.

Formalization stopped being a job for one team over years: the step
between "LTE, two years" and "Fermat, eleven days".
:::

# Equational Theories, 2024-25

{image "../static/figures/portraits/tao.jpg" (class := "portrait")}[Terence Tao]

:::class "names"
Terence Tao
:::

:::fitText
22 028 942 implications between 4 694 laws.
:::


:::notes
All implications between equational laws on magmas, settled, with new
constructions found on the way.

The difficulty is not depth but bookkeeping, on a scale that needs a
machine.
:::

# Sphere packing, dim. 8 and 24

:::hstack
{image "../static/figures/e8_roots.png" (height := "30vh")}[The 240 roots of E8 in the Coxeter plane]

{image "../static/figures/portraits/viazovska.jpg" (class := "portrait")}[Maryna Viazovska]
:::

:::class "names"
Maryna Viazovska
:::

:::notes
Viazovska 2016, Fields Medal 2022. The packing is the E8 lattice; these
are its 240 shortest vectors.

Human formalization project from 2024, finished by an autoformalizer in
February 2026 -- dimension 8 in five days. This is the February entry
from the 2026 slide; it belongs to both stories.

This closes the thread that opened with Kepler, four hundred years
earlier.
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

# Mathlib

One library, one repository, one version. Everything in this course imports it.

:::fragment fadeUp
[The library itself](https://github.com/leanprover-community/mathlib4)
:::

:::fragment highlightBlue
[The interactive import map](https://leanprover-community.github.io/mathlib4_docs/mathlib.html) -- the whole of *Mathlib* as a graph of its areas.
:::

:::notes
Open the import map live and let them look at it: one connected
library, not a pile of packages. That is why we use Lean and not Rocq.

Point at a node, follow an edge, show how analysis sits on order sits
on algebra.
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

# Wednesday

:::fitText
Bring a laptop. With administrator rights.
:::

:::fragment fadeUp
Follow the instructions to [install Lean and Mathlib](https://leanprover-community.github.io/get_started.html) beforehand.
:::

:::fragment fadeUp
The full list is in the [course notes](https://pfaffelh.github.io/leancourse/), at the end of the first chapter.
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

