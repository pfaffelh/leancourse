-- This module serves as the root of the `Leancourse` library.
-- Import modules here that should be built as part of the library.
import VersoManual
import Mathlib

import «Leancourse».Coursenotes.«01-Lean»
import «Leancourse».Coursenotes.«03-Mathematics»
import «Leancourse».Coursenotes.«04-Appendix»
import «Leancourse».Coursenotes.«05-Projects»
import «Leancourse».Coursenotes.«99-Bibliography»

open Verso.Genre Manual

#doc (Manual) "Interactive Theorem Proving using Lean, Winter 2026/27" =>
%%%
tag := "ITPFr"
authors := ["Peter Pfaffelhuber"]
%%%

These are the notes for a course on formal proving with the interactive theorem prover Lean4 (in the following we just write Lean) in the winter semester of 2026/27 at the University of Freiburg. To be able to work through the course in a meaningful way, the following technical preparations are to be made:

*Hardware.* Check first that your machine can carry this. Lean memory-maps all of *Mathlib* while it works, and every exercise sheet begins with `import Mathlib`. A two-line sheet therefore costs as much as the hardest one in the course.

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

Measured against the version of *Mathlib* used here: compiling a single sheet peaks at about 6.6 GB of resident memory, and the language server behind *vscode* sits at roughly 9 GB with one file open. Most of that is memory-mapped library data, which the system can drop and read back from disk, so less memory does not break anything -- it only makes everything slower. With 8 GB you can still work, but only with a single file open and little else running, and on a mechanical hard disk it is hopeless.

*If your machine is below the minimum, talk to the teachers at the start of the course.* A server with 128 GB of RAM is available for this course and we can give you an account on it. Please do not try to get through the semester on a machine that fights you.

Finally, please run the `git clone` and `lake exe cache get` below at home, before the first lab session. `lake exe cache get` downloads several gigabytes, and twenty people doing that at once on the same network is slow for all of them.

* Installation of [vscode](https://code.visualstudio.com/).
* Open `vscode`, hit the _extensions_ icon (fifth from the top) on the left, and install the _Lean 4 language extension_.
* If you haven't done already, install `git`. For this, the best way is to open `vscode`, hit the _git_ icon (third from the top on the left), and follow the instructions.
* Installing the exercises repository: Navigate to a location where you would like to put the course materials and use
```
git clone https://github.com/pfaffelh/leancourse_exercises
cd leancourse_exercises
lake exe cache get
code .
```
Then, _vscode_ should open and you see the course materials. (The exercises live in their own repository; the course notes you are reading are generated from [pfaffelh/leancourse](https://github.com/pfaffelh/leancourse), which you do not need to clone.)

:::paragraph
Note: Yet another description how to install _Lean_ is found [here](https://leanprover-community.github.io/get_started.html#regular-install).
:::


After having typed `code .` within the `leancourse_exercises` folder, navigate to `Exercises/01-Logic/01-a-Propositions.lean`. Everything is fine once orange and/or red bars disapprear, and navigating in the left hand side of the windom leads to changes in the right hand side (the infoview). You should see some code which looks a bit like mathematics.
* The directory `Exercises` contains the material for the course. We recommend that you first copy this directory to `MyExercises` and work there: `MyExercises` is ignored by git, so an update of the repository will never overwrite your local files.
* To update the course materials, enter `git pull` from within the `leancourse_exercises` directory.

If you have trouble installing the course material on your own computer, please talk to the teachers. Do not spend your evenings fighting your laptop -- see the note on hardware above.

*Goals.* The course is designed for mathematics students and has several goals:

* Learning the techniques for interactive theorem proofing using Lean: In recent years, efforts to prove mathematical theorems with the help of computers have increased dramatically. While a few decades ago, it was more a matter of consistently processing many cases that were left to the computer, interactive theorem provers are different. Here, a very small core can be used to understand or interactively generate all the logical conclusions of a mathematical proof. The computer then reports interactively on the progress of the proof and when all the steps have been completed.
* Establishing connections to some mathematical material: At least in the first half, the mathematical details needed in this course should not be the main issue of this course. However, in order to _explain_ how a proof (or calculation or other argument) to a computer, you first have to understand it very well yourself. Furthermore, you have to plan the proof well - at least if it exceeds a few lines - so that the commands you enter (which we will call tactics) fit together. The course intends to teach both, first steps in `Lean` and learning a bunch of these tactics, and make a deeper dive into some mathematical material.
* Understanding functional programming: Lean is not only a theorem prover but also a functional programming language. We cover core concepts such as inductive types, structures, typeclasses, and monads, which are essential both for using Lean effectively and for understanding how Mathlib is organized. These topics are distributed across the Lean and Mathematics parts of the notes rather than collected into a chapter of their own.
* Learning type theory: The foundation of Lean is dependent type theory. We explore the Curry-Howard correspondence, dependent types, the universe hierarchy, and the axioms underlying Lean, providing the theoretical background for why interactive theorem proving works.
* Exploring advanced mathematics in Lean: We survey how Mathlib organizes order theory, the algebraic hierarchy, filters (which provide a unified framework for limits), topology, measure theory, and discrete probability. These topics are not always well covered in standard textbooks from the perspective of formalization.
* Proof engineering: We learn to use powerful automation tactics, navigate Mathlib effectively, and avoid common pitfalls when working with a large formal library.

*Why formalize?* Three episodes make the case better than an argument would. (A [slide deck](slides/introduction/) covers this section and the two that follow it, for the first lecture.)

In 1976 Kenneth Appel and Wolfgang Haken proved the four colour theorem. Their argument reduced the problem to a long list of configurations and then checked that list by computer. No human has ever read that part, and for two decades the community argued about whether it counted as a proof at all. In 2005 Georges Gonthier ended the argument from the other side: he formalized the whole thing, case analysis included, in Coq. The distinction those two events separate is the one this course rests on -- *a proof found by computer is not the same thing as a proof checked by computer.*

In 1998 Thomas Hales announced a proof of the Kepler conjecture: no packing of equal spheres in space is denser than the way a greengrocer stacks oranges.

:::figure "The packing Kepler conjectured to be optimal in 1611" (tag := "kepler")
![A pyramid of equal spheres, the face-centred cubic packing, with density pi over root 18](/static/figures/kepler_packing.png)
:::

A panel of twelve referees worked on it for four years and then reported that they were ninety-nine percent certain of its correctness, and that they could not do better than that. The *Annals of Mathematics* published it with the caveat attached. Hales responded by starting the Flyspeck project, which delivered a complete formal proof in HOL Light and Isabelle in 2014. The lesson here is not about computers: peer review, the mechanism mathematics relies on, had met a proof it could not certify, and more effort was not going to change that.

In December 2020 Peter Scholze posed a challenge on Kevin Buzzard's blog. He had a theorem in condensed mathematics whose proof he was not sure of -- a Fields medallist, publicly unsure of his own argument, asking for a machine to check it. The *Liquid Tensor Experiment*, led by Johan Commelin, finished in July 2022. Buzzard's plenary lecture at the ICM in 2022 is a fair marker for the moment formalization stopped being a curiosity.

*A short prehistory.* The idea is much older than the tools. Gottlob Frege's *Begriffsschrift* of 1879 gave the first system in which proofs themselves were objects to be manipulated; Bertrand Russell's letter of 1902 showed that the system was inconsistent. Whitehead and Russell spent *Principia Mathematica* rebuilding, and their proof that `1 + 1 = 2` arrives in the second volume with the authors' note that *the above proposition is occasionally useful*. Done by hand, formalization is unbearable, and for most of a century little came of it. De Bruijn's *Automath* (1967) was the first system to check proofs mechanically, and in 1977 van Benthem Jutting pushed Landau's *Grundlagen der Analysis* through it -- the first complete mathematics book verified by machine.

Lean itself is recent. Leonardo de Moura started it at Microsoft Research in 2013. Lean 4, a redesign rather than a version bump, arrived in 2021, and development now sits with the Lean FRO, a non-profit of roughly twenty people. Kevin Buzzard has been making the case for Lean among mathematicians since 2018.

*Landmark formalizations.* Between Flyspeck and 2026 lies a line of projects that each showed that something new was possible. They are worth knowing by name, because the course material is built out of the libraries they left behind.

* *Perfectoid spaces*, 2019, by Buzzard, Commelin and Massot. They did not prove a theorem; they formalized a *definition* from the research frontier, Scholze's perfectoid spaces of 2012. Whether an object of that complexity could even be stated in a proof assistant was genuinely open, and stating something is a different problem from proving it. This is where Lean's reputation among mathematicians begins.
* *Sphere eversion*, 2022, by Massot, van Doorn and Nash: Gromov's h-principle, and with it the fact that a sphere can be turned inside out. Differential topology rather than algebra or combinatorics, which meant first building a usable differential-geometry API and only then proving anything with it. That is the ordinary shape of formalization work, and it is why *Mathlib* matters more than any single theorem in it.
* *The polynomial Freiman-Ruzsa conjecture*, 2023, by Gowers, Green, Manners and Tao, formalized under Tao's direction in about three weeks -- before the paper had been refereed. The method is what carried: a *blueprint* cuts a formalization into independent pieces with stated interfaces, so that volunteers can work in parallel without talking to each other. Formalization stopped being a job for one team over years.
* *The Equational Theories Project*, 2024 to 2025, led by Tao: all 22 028 942 implications between 4 694 equational laws on magmas settled, and new constructions discovered on the way. Not a hard theorem but an impossible amount of bookkeeping -- a kind of result that does not exist without a machine.
* *Sphere packing in dimensions 8 and 24*. Viazovska proved the dimension-8 case in 2016 and received the Fields Medal for it; a human formalization project started in 2024 and was completed with an autoformalizer in February 2026, the eight-dimensional proof in five days. The thread that opens with Kepler above closes here, four hundred years later and one dimension at a time.

*What changed in 2026.* Until recently, formalizing a serious theorem took a team and several years. That is no longer the constraint, and the change happened quickly enough that it is worth writing down with dates.

* *4 September 2026.* Anthropic announced the first complete computer-checked proof of Fermat's Last Theorem, produced by Claude over eleven days: roughly 13 million lines of Lean and some 29 500 intermediate theorems, following a simplified version of Wiles's 1995 proof and building on *Mathlib*. Kevin Buzzard, who has led the community formalization effort since 2024 on a five-year grant, reviewed it and confirmed that it *proves Fermat's Last Theorem with no assumptions other than the axioms of mathematics*. Note the shape of that confirmation: it is a claim a machine can check, and you will meet the command that checks it -- `#print axioms` -- in this course.
* *8 September 2026.* OpenAI announced a proof, with a Lean formalization, that a smooth three-dimensional fluid obeying the Navier-Stokes equations *under a smooth external force* can develop a singularity in finite time. This is not the Millennium Prize problem, which concerns the unforced equation, and the prize is unclaimed. The announcement was followed by a public argument among mathematicians about credit, and about what it does to the subject when open problems are treated as benchmarks.
* *6 October 2026.* OpenAI published a catalogue of results from an unreleased internal model -- at the time of writing 719 manuscripts grouped into 372 families, of which about 42 % of the top-line results carry a Lean formalization. Each result took, on average, about three hours of the model's thinking time; roughly 4 000 problems were posed in all.
* *7 October 2026.* One day later, three of those manuscripts were withdrawn: a sign error invalidated an argument in one, and two further papers depended on it. Fourteen more were revised. None of the withdrawn papers had a Lean proof.

Those last two dates are the best argument for this course we could have asked for. Machines now produce mathematics faster than mathematicians can referee it, and the only check that keeps up is a formal one.

But be precise about what that check buys. A Lean proof certifies that *a particular formal statement* follows from the axioms. Whether that formal statement is the theorem the paper claims is a different question, and a human one. OpenAI's own repository is careful here: it ships machine-checkable comparison setups and documents, per paper, which of them verify a main theorem and which only verify a supporting result. Reading a formal statement and judging whether it says what you think it says is a skill. It is, in large part, the skill this course teaches.

*Where the field stands.* Two pictures, both from public data.

:::figure "New GitHub repositories per quarter, per million new repositories overall" (tag := "itp-repos")
![Line chart: new GitHub repositories per quarter for Lean, Coq/Rocq and Isabelle from 2018 to 2026, each per million new repositories overall; Lean rises from under ten to about two hundred while the others stay near ten](/static/figures/itp_github_repos_per_million.png)
:::

The counts are given per million new repositories overall, because the absolute numbers mislead at the right-hand edge: in September 2026 the number of new repositories on GitHub rose by 37 % in a single month, which has nothing to do with Lean. One distortion is left in deliberately. The Justin Sun Prize, announced on 16 September 2026, pays up to a million dollars for a solved problem but only against a machine-verified proof; 666 of that month's 3 224 new Lean repositories carry a prize identifier, and a single account created 284 of them. Strip the prize repositories and the near-empty ones out, and the growth from August to September is a factor of 1.5 rather than 2.

Until about 2023 the three systems were comparable, and Coq was the larger one. The curve that leaves the picture is recent, and it is not evidence that Lean is better -- Isabelle's automation is still ahead in places, and Rocq has decades of verified-software work behind it. It is evidence about where people are going.

:::figure "arXiv papers per week whose results are checked in Lean" (tag := "arxiv-lean")
![Bar chart: weekly count of arXiv papers with Lean-checked results during 2026, rising from about three per week in January to around forty per week in September](/static/figures/arxiv_lean_formalized_weekly.png)
:::

In January 2026 a handful of papers a week arrived with a machine-checked result; by September it was around forty. This is the development that makes a course like this one worth your time: within a few years, being able to read and write a formal proof will be an ordinary part of the mathematician's equipment, in the way that being able to use a computer algebra system already is.

*Other theorem provers.* Lean is not the only one, and the two it is usually compared with differ from it in ways worth knowing, because the differences are about foundations rather than taste.

:::table (align := left) +header
* + System
  + Foundation
  + Dependent types
  + Library
* + Lean 4
  + a variant of the Calculus of Inductive Constructions
  + yes
  + *Mathlib*, one repository
* + [Rocq](https://rocq-prover.org/) (until 2025 *Coq*)
  + the predicative Calculus of Cumulative Inductive Constructions
  + yes
  + many separate packages
* + [Isabelle/HOL](https://isabelle.in.tum.de/)
  + simply typed higher-order logic
  + no
  + the *Archive of Formal Proofs*
:::

*Lean and Rocq* are close relatives. Both rest on a dependent type theory in which a proof is a *term* and checking a proof is type-checking; both have an impredicative, proof-irrelevant universe `Prop` of propositions sitting under a predicative hierarchy of data types. Lean differs in four points that you will meet again later in these notes: proof irrelevance holds *definitionally*, quotient types are primitive rather than built from setoids, there is no universe cumulativity, and classical reasoning enters through an axiom (`Classical.choice`) rather than being absent by default. Rocq's roots are in program verification -- the CompCert C compiler and the Feit-Thompson theorem are both Rocq developments -- and it can extract verified programs to OCaml or Haskell.

*Isabelle/HOL* is a different animal. Its logic is simple type theory: types are built from base types and arrows, there is no dependency of types on terms, and so one cannot write `Vec α n` for *lists of length `n`*. In exchange, the logic is weak enough to automate well, and Isabelle's automation remains the best in the field: *Sledgehammer* hands a goal to several external automatic provers at once and reconstructs whatever they find as a proof Isabelle itself can check. A good deal of what Lean's `grind` does, Isabelle has done for twenty years. Isabelle is also a *framework*: HOL is one object logic among several, built on the intuitionistic meta-logic Isabelle/Pure. Its flagship is *seL4*, an operating-system microkernel verified down to its C implementation and still the largest piece of verified systems software in existence.

*How the libraries are organized* differs just as much, and this matters more day to day than the foundations do.

* *Mathlib* is a single repository holding essentially all of the mathematics, compiled as one unit, with every change reviewed by maintainers and continuous integration keeping the whole library building against the current Lean. The price is that there is no stable release to depend on: *Mathlib* tracks Lean, and your own development must track *Mathlib*. The gain is that everything composes. A theorem about topological groups can be applied to the reals without anyone having arranged for it, because there is only one hierarchy of structures and the reals sit inside it. That hierarchy, built out of `class` and `instance`, is what the chapters on typeclasses and the algebraic hierarchy are about.
* *Rocq* has no such centre. Its standard library is deliberately small, and the mathematics lives in independent packages -- *MathComp*, grown out of the Feit-Thompson formalization, *Coquelicot* and *MathComp-Analysis* for analysis, and many more -- distributed through `opam`, with the *Rocq Platform* bundling a combination that has been tested together. Packages evolve at their own pace, which is comfortable if you depend on one of them and painful if you need two that disagree.
* *Isabelle* sits in between. The *Archive of Formal Proofs* is a refereed archive of self-contained entries, each released in lockstep with Isabelle itself, which may depend on one another but are never merged into a single library. It reads like a journal of formalizations, and it is cited like one.

For this course the practical consequence is simple: we use Lean because *Mathlib* exists, and *Mathlib* is the reason the exercises can start with `import Mathlib` and have the real numbers, measure theory and topology already there.

*Other courses.* This is not the only course trying to teach Lean to you. Others worth a look:

* [_Natural Number Game_](https://adam.math.hhu.de/#/g/leanprover-community/nng4): In case you are reading this text in advance and have some spare time, it is highly recommended to start this (online) game, making you prove first things on `ℕ` using Lean. It is a classical way to start your first contact with Lean.
* [_Formalising Mathematics_](https://b-mehta.github.io/formalising-mathematics-notes/) by Bhavik Mehta, based on notes by Kevin Buzzard: these notes have inspired at least the format of the present course.
* [_Mathematics in Lean_](https://leanprover-community.github.io/mathematics_in_lean/) by Jeremy Avigad and Patrick Massot: if there is something like an official course maintained by experts in charge, this is probably it. It is mainly concentrated about different areas of mathematics.

*Some notes on Lean and Mathlib.*

* Lean is not only an interactive theorem prover, but also a programming language. If you want to know/learn more about this aspect, please consult [Functional programming in Lean](https://lean-lang.org/functional_programming_in_lean/).
* While `Lean` is a programming language, [*Mathlib*](https://github.com/leanprover-community/mathlib4) is a library written in it. It collects various (more or less deep) mathematical results. In this course, we do not make any distinction between `Lean` and `Mathlib`, since we will have `import Mathlib` at the start of any file we will need results from there. In this way, we have access to a large part of mathematics in order to solve exercises.
* How big is that? Measured on the version pinned for this course (15 September 2026): 8 529 files, 2.33 million lines, about 189 000 theorems and lemmas, about 64 000 definitions, instances and structures, written by 1 031 contributors in 34 768 commits. The number that matters most is a different one: in the thirty days before that date, *Mathlib* received 820 commits, which is 27 per day. The others say that it is big; this one says that it is alive.
* You can look at the whole thing at once. The [interactive import map](https://leanprover-community.github.io/mathlib4_docs/mathlib.html) draws *Mathlib* as a graph of its modules and lets you zoom in on any of them; the same site serves the [API documentation](https://leanprover-community.github.io/mathlib4_docs/) for every declaration in the library. Both are worth half an hour early on, before you need them.

*How the course is organized.* Unlike a textbook, this course interleaves tactics and theory rather than separating them. Concretely:

* The first part, *Lean and its type theory*, introduces both tactical reasoning (writing proofs) and the dependent type theory that underlies it.
* Tactics are documented *alphabetically* in a glossary in the *Appendix*, not woven into the narrative. You will often meet a tactic in a working example before you read its entry; a preview table at the start of *Proofs in Lean* lists the ones you will need first.
* We recommend reading in order, but on a first pass it is fine to skip the tactics chapter and consult it when you hit a `sorry` proof.

*How to use this course.* These notes are organized into the following parts, followed by a reference appendix and a bibliography:

* *Lean and its type theory*: Lean both as a proof assistant and as a dependent type theory. We start hands-on -- the language, writing proofs, the functional-programming side of Lean (pure functions, pattern matching, recursion, higher-order functions), and navigating Mathlib. We then turn to the theory: the Curry-Howard correspondence, dependent types, universes, the three axioms of Lean (and what the kernel additionally bakes in), the `structure` / `class` machinery that underpins Mathlib, and well-foundedness and the avoidance of paradoxes.
* *Mathematics*: after an opening chapter on the everyday foundations -- propositions, proofs, and sets -- we survey how Mathlib organizes order theory, the algebraic hierarchy, filters, topology, measure theory, and monadic discrete probability (`PMF`), with pointers into the relevant Mathlib API rather than full formalizations.
* *Appendix*: common pitfalls when working with Lean and Mathlib, the diagnostic commands (`#print axioms`, `#find_home`, `#lint`), an alphabetical keyword reference, and an *alphabetical glossary of tactics* (an even longer list lives [here](https://github.com/haruhisa-enomoto/mathlib4-all-tactics/blob/main/all-tactics.md)).
* *Projects*: five suggested topics for the individual formalization projects in the second half of the course, each with a description, a sketch of a possible implementation, and references.
* *Bibliography*: the works cited throughout, with links.

The heart of the course are the exercises (see the _Exercises_ folder within `Leancourse`). Unlike in other courses, you will get immediate feedback on any single exercise -- via error messages from the elaborator and a live *proof-state* panel that shows what remains to be proved at every cursor position. If you want to start right away, please start immediately with the first exercise sheet. More explanations will be given within the exercise sheets.

While the exercises will cover the first half of the semester, individual assignments will happen in the latter part of this course. (These will mostly be self-assigned, so e.g. you will formalize an exercise from your first year of studies, or you are interested in a specific part of `Mathlib`, or... The {ref "projects"}[Projects chapter] collects five worked-out suggestions.)

{include 0 «Leancourse».Coursenotes.«01-Lean»}

{include 0 «Leancourse».Coursenotes.«03-Mathematics»}

{include 0 «Leancourse».Coursenotes.«04-Appendix»}

{include 0 «Leancourse».Coursenotes.«05-Projects»}

{include 0 «Leancourse».Coursenotes.«99-Bibliography»}
