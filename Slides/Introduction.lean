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

# Why formalize?

:::fitText
A proof *found* by computer is not a proof *checked* by computer.
:::

:::notes
This is the whole lecture in one line. Everything that follows is
an illustration of it. Come back to it at the end.
:::

# Three episodes

:::fragment fadeUp
- 1976 -- the four colour theorem
:::

:::fragment fadeUp
- 1998 -- the Kepler conjecture
:::

:::fragment fadeUp
- 2020 -- the Liquid Tensor Experiment
:::

:::notes
Not chronology for its own sake. Each one makes a different point:
what a computer proof is worth, where peer review stops, and who is
asking for this now.
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

:::notes
Two decades of argument about whether this counted as a proof.
Gonthier did not settle the argument; he made it unnecessary.
:::

# 1998: stacking oranges

{image "../static/figures/kepler_packing.png"}[A pyramid of equal spheres, the face-centred cubic packing]

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

# 2020: a Fields medallist is unsure

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

:::notes
Lean itself: de Moura, Microsoft Research, 2013. Lean 4 in 2021.
Lean FRO, about twenty people. Buzzard campaigning since 2018.
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

:::notes
Installation session. VS Code, the Lean extension, git clone,
`lake exe cache get`. Ask them to try it at home first.
:::
