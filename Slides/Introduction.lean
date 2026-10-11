import VersoSlides
import Verso.Doc.Concrete
import Mathlib

open VersoSlides

set_option pp.rawOnError true

/-
Deck for the first lecture (week 1, Monday).  It follows the opening
chapter of the course notes section by section, so that the two can be
shown together: *Why formalize?*, the prehistory, what changed in 2026,
and where the field stands.  The claims and figures are the same ones.
-/

#doc (Slides) "Why formalize?" =>

```css
img.portrait {
  width: 92px; height: 92px; object-fit: cover; object-position: 50% 20%;
  border-radius: 50%; margin: 0 0.3rem; vertical-align: middle;
  box-shadow: 0 1px 5px rgba(0, 0, 0, 0.2);
}
.names { font-size: 0.45em; color: #52514e; letter-spacing: 0.02em;
         margin-top: 0.1em; }
.reveal section img { margin: 0.4rem 0; }
.reveal section img.logo {
  width: auto; margin: 0 1.6rem; vertical-align: middle;
}
/* ANTHROPIC is all caps, OpenAI has ascenders and a descender, so
   equal box heights look unequal; match the capital letters instead */
.reveal section img.logo-anthropic { height: 4.2vh; }
.reveal section img.logo-openai    { height: 5.4vh; }
```

# Why formalize?

:::fitText
A proof *found* by computer is not a proof *checked* by computer.
:::

:::notes
This is the whole lecture in one line. Everything that follows is
an illustration of it. Come back to it at the end.
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
This is the definition, and it is the whole of it. Everything that
follows in this lecture is motivation for caring about it.
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

{image "../static/figures/logos/anthropic.png" (class := "logo logo-anthropic")}[Anthropic] {image "../static/figures/logos/openai.png" (class := "logo logo-openai")}[OpenAI]

:::notes
FLT: Anthropic, Claude, building on Mathlib, following a simplified
Wiles. Buzzard confirmed it assumes nothing but the axioms.

Navier-Stokes: the *forced* equation. Not the Millennium problem.
The prize is unclaimed. Say this plainly.

The last two dates belong together -- next slide.
:::

# One day apart

:::fitText
None of the withdrawn papers had a Lean proof.
:::

:::notes
Machines now produce mathematics faster than mathematicians can
referee it. The only check that keeps up is a formal one.

This is the argument for the course. Do not oversell it -- the next
slide takes it back a step.
:::

# But be precise

A Lean proof certifies that *a formal statement* follows from the axioms.

:::fragment fadeUp
Whether that statement is the theorem in the paper is a *human* question.
:::

:::fragment highlightBlue
Reading a formal statement and judging what it says is a skill.
It is most of what this course teaches.
:::

:::notes
OpenAI's own repository documents, per paper, which checks cover a
main theorem and which only a supporting result. That honesty is the
model to point at.
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
That was the state of things. Now how it got there, in order.

Not chronology for its own sake: each episode adds a different reason.
What a computer proof is worth, where peer review stops, whether the
author can trust himself, and who is asking for this now.
:::

# The idea is old

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

{image "../static/figures/portraits/demoura.jpg" (class := "portrait")}[Leonardo de Moura]

:::class "names"
Leonardo de Moura, who started Lean in 2013
:::

:::notes
Lean itself: de Moura, Microsoft Research, 2013. Lean 4 in 2021.
Lean FRO, about twenty people. Buzzard campaigning since 2018.
:::

# 1976: four colours

Appel and Haken reduce the problem to a long list of configurations.

A computer checks the list.

:::fragment fadeUp
*No human has ever read that part.*
:::

:::fragment highlightBlue
2005: Gonthier formalizes all of it in Coq -- case analysis included.
:::

{image "../static/figures/four_colour.png" (height := "32vh")}[A map of thirty-four regions coloured with four colours]

{image "../static/figures/portraits/placeholder_gonthier.png" (class := "portrait")}[Georges Gonthier]

:::class "names"
Georges Gonthier
:::

:::notes
Two decades of argument about whether this counted as a proof.
Gonthier did not settle the argument; he made it unnecessary.
:::

# 1998: stacking oranges

{image "../static/figures/kepler_packing.png" (height := "34vh")}[A pyramid of equal spheres, the face-centred cubic packing]

{image "../static/figures/portraits/hales.jpg" (class := "portrait")}[Thomas Hales]

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
This is the strongest of the three, and it is not about computers.
Peer review met a proof it could not certify. More effort would not
have helped.
:::

# 1989: a theorem about higher groupoids

Voevodsky and Kapranov identify $`\infty`-groupoids with homotopy types.

:::fragment fadeUp
*Oct 1998* -- Simpson posts an argument that it cannot be true.
:::

:::fragment highlightBlue
*Autumn 2013* -- Voevodsky accepts that Simpson was right.
:::

{image "../static/figures/portraits/voevodsky.jpg" (class := "portrait")}[Vladimir Voevodsky]

:::class "names"
Vladimir Voevodsky
:::

:::notes
Fifteen years. Not an obscure corner either -- both authors were well
known, and Voevodsky got the Fields Medal in between, in 2002.

The point is not that they made a mistake. Everyone does. The point is
how long it took to resolve, and why.
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

So he went looking for a proof assistant, found none he could use, and
built the foundations for one -- univalent foundations, the IAS special
year 2012-13, the HoTT book. In Coq, not Lean; and not the foundations
Mathlib uses. We take the diagnosis, not the cure. He died in 2017.
:::

# 2020: a Fields medallist is unsure

Scholze posts a challenge on Buzzard's blog.

He is not certain of his own theorem.

:::fragment fadeUp
Liquid Tensor Experiment, led by Commelin. Finished July 2022.
:::

:::fragment fadeUp
Not combinatorics with a thousand cases -- condensed mathematics.
:::

{image "../static/figures/cantor_profinite.png" (height := "22vh")}[Seven stages of the middle-thirds construction]

{image "../static/figures/portraits/scholze.jpg" (class := "portrait")}[Peter Scholze] {image "../static/figures/portraits/placeholder_commelin.png" (class := "portrait")}[Johan Commelin]

:::class "names"
Peter Scholze, Johan Commelin
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
out of the libraries they left behind -- that is why they are named.
:::

# Perfectoid spaces, 2019

{image "../static/figures/padic_tree.png" (height := "30vh")}[The 3-adic integers as a ternary tree]

:::fragment highlightBlue
They formalized a *definition*, not a theorem.
:::

{image "../static/figures/portraits/buzzard.jpg" (class := "portrait")}[Kevin Buzzard] {image "../static/figures/portraits/placeholder_commelin.png" (class := "portrait")}[Johan Commelin] {image "../static/figures/portraits/placeholder_massot.png" (class := "portrait")}[Patrick Massot]

:::class "names"
Kevin Buzzard, Johan Commelin, Patrick Massot
:::

:::notes
Scholze's perfectoid spaces, 2012. Whether an object of that complexity
could even be *stated* in a proof assistant was open. Stating is a
different problem from proving.

This is where Lean's reputation among mathematicians begins.
:::

# Sphere eversion, 2022

{image "../static/figures/turning_number.png" (height := "26vh")}[Four closed plane curves with their turning numbers]

:::fragment fadeUp
In the plane the turning number blocks it: $`+1` cannot become $`-1`.
:::

:::fragment highlightBlue
In three dimensions the obstruction is gone.
:::

{image "../static/figures/portraits/placeholder_massot.png" (class := "portrait")}[Patrick Massot] {image "../static/figures/portraits/placeholder_vandoorn.png" (class := "portrait")}[Floris van Doorn] {image "../static/figures/portraits/placeholder_nash.png" (class := "portrait")}[Oliver Nash]

:::class "names"
Patrick Massot, Floris van Doorn, Oliver Nash
:::

:::notes
Gromov's h-principle. Differential topology, not algebra -- so the
project had to build a differential-geometry API first and prove
anything only afterwards.

That is the ordinary shape of formalization work, and the reason
Mathlib matters more than any single theorem in it.
:::

# Freiman-Ruzsa, 2023

{image "../static/figures/sumset.png" (height := "22vh")}[A set of small doubling beside its sumset]

:::fragment fadeUp
Formalized in about three weeks -- *before* the paper was refereed.
:::

{image "../static/figures/portraits/gowers.jpg" (class := "portrait")}[Timothy Gowers] {image "../static/figures/portraits/green.jpg" (class := "portrait")}[Ben Green] {image "../static/figures/portraits/tao.jpg" (class := "portrait")}[Terence Tao] {image "../static/figures/portraits/placeholder_manners.png" (class := "portrait")}[Freddie Manners]

:::class "names"
Timothy Gowers, Ben Green, Terence Tao, Freddie Manners
:::

:::notes
The method is what carried. A *blueprint* cuts a formalization into
independent pieces with stated interfaces, so volunteers can work in
parallel without talking to each other.

Formalization stopped being a job for one team over years. This is the
missing step between "LTE, two years" and "Fermat, eleven days".
:::

# Equational Theories, 2024-25

:::fitText
22 028 942 implications between 4 694 laws.
:::

{image "../static/figures/portraits/tao.jpg" (class := "portrait")}[Terence Tao]

:::class "names"
Terence Tao
:::

:::notes
All implications between equational laws on magmas, settled, with new
constructions found on the way.

Not a hard theorem -- an impossible amount of bookkeeping. A kind of
result that does not exist without a machine.
:::

# Sphere packing, dim. 8 and 24

{image "../static/figures/e8_roots.png" (height := "34vh")}[The 240 roots of E8 in the Coxeter plane]

{image "../static/figures/portraits/viazovska.jpg" (class := "portrait")}[Maryna Viazovska]

:::class "names"
Maryna Viazovska
:::

:::notes
Viazovska 2016, Fields Medal 2022. The packing is the E8 lattice; these
are its 240 shortest vectors.

Human formalization project from 2024, finished by an autoformalizer in
February 2026 -- dimension 8 in five days.

This closes the thread that opened with Kepler. Four hundred years, one
dimension at a time.
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
This is the slide that answers "why should I spend a semester on
this". Within a few years, reading and writing a formal proof will
be ordinary equipment.
:::

# Three systems

:::fragment fadeUp
- *Lean 4* -- dependent types, one library: Mathlib
:::

:::fragment fadeUp
- *Rocq* (until 2025 Coq) -- dependent types, many packages
:::

:::fragment fadeUp
- *Isabelle/HOL* -- simple type theory, no dependent types, the best automation
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

# Wednesday

:::fitText
Bring a laptop. With administrator rights.
:::

:::fragment highlightBlue
And run `lake exe cache get` *before* you come.
:::

:::notes
Installation session. VS Code, the Lean extension, git clone,
`lake exe cache get`. Ask them to try it at home first.

Say the last point twice. `lake exe cache get` downloads the compiled
Mathlib; without it every machine in the room compiles Mathlib from
source at the same time, which takes hours and kills the session.
:::

