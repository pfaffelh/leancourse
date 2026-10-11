-- This module serves as the root of the `Leancourse` library.
-- Import modules here that should be built as part of the library.
import VersoManual
import Manual.Meta
import Mathlib

import «Leancourse».Coursenotes.«01-Lean»
import «Leancourse».Coursenotes.«03-Mathematics»
import «Leancourse».Coursenotes.«04-Appendix»
import «Leancourse».Coursenotes.«05-Projects»
import «Leancourse».Coursenotes.«99-Bibliography»

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

#doc (Manual) "Interactive Theorem Proving using Lean, Winter 2026/27" =>
%%%
tag := "ITPFr"
authors := ["Peter Pfaffelhuber"]
%%%

Notes for a course on formal proving with the interactive theorem prover Lean 4 (below simply Lean), winter semester 2026/27, University of Freiburg. Hardware, installation and the run of the semester are at the end of this chapter.

*What formalizing means.* To formalize a proof is to write it in a language precise enough that a computer can check every step. The machine does not look for the proof. It reads the one you give it and confirms that each step follows from the axioms and from what came before. Anything left out is refused.

*Finding a proof is not checking one.* In 1976 a computer checked a long list of cases in the four colour theorem. The argument around that list was ordinary mathematics on paper, and nothing checked it.

*Autoformalizing goes the other way.* Formalizing starts from a proof and ends in a formal text. Autoformalizing starts from informal mathematics -- a statement, a paper -- and has a machine produce that text. Both end at the same place, a text the kernel accepts. The program that writes a proof may be unreliable in any way it likes; the program that checks it is small and fixed.

This course is about the first direction. You will write the proofs.

*Why formalize?* Until recently, formalizing a serious theorem took a team and several years. That is no longer so, and the change is recent enough to date precisely.

* *February 2026.* The [sphere packing](https://en.wikipedia.org/wiki/Sphere_packing) theorem in dimension 8 was finished by an autoformalizer in five days. A human project had been working on it since 2024. It is the first of these results and the clearest: the mathematics was settled, so only the formalizing was left.
* *4 September 2026.* Anthropic announced the first complete computer-checked proof of [Fermat's Last Theorem](https://en.wikipedia.org/wiki/Fermat%27s_Last_Theorem), produced by Claude over eleven days: roughly 13 million lines of Lean and some 29 500 intermediate theorems, following a simplified version of Wiles's 1995 proof and building on *Mathlib*. Kevin Buzzard, who has led the community formalization effort since 2024 on a five-year grant, reviewed it and confirmed that it *proves Fermat's Last Theorem with no assumptions other than the axioms of mathematics*. That confirmation is itself machine-checkable, by `#print axioms` (Appendix).
* *8 September 2026.* OpenAI announced a proof, with a Lean formalization, that a smooth three-dimensional fluid obeying the [Navier-Stokes equations](https://en.wikipedia.org/wiki/Navier%E2%80%93Stokes_existence_and_smoothness) *under a smooth external force* can develop a singularity in finite time. This is not the Millennium Prize problem, which concerns the unforced equation, and the prize is unclaimed. It was followed by a public argument about credit, and about treating open problems as benchmarks.
* *6 October 2026.* OpenAI published a catalogue of results from an unreleased internal model -- at the time of writing 719 manuscripts grouped into 372 families, of which about 42 % of the top-line results carry a Lean formalization. Each result took, on average, about three hours of the model's thinking time; roughly 4 000 problems were posed in all.
* *7 October 2026.* One day later, three of those manuscripts were withdrawn: a sign error invalidated an argument in one, and two further papers depended on it. Fourteen more were revised. None of the withdrawn papers had a Lean proof.

:::figure "The two systems behind the September 2026 announcements. Both delivered Lean files with their proofs" (tag := "ai-labs")
![Claude](/static/figures/logos/claude.png)

![ChatGPT](/static/figures/logos/chatgpt.png)
:::

Those last two dates belong together. Machines now produce mathematics faster than mathematicians can referee it, and the only check that keeps up is a formal one.

A formal check is narrower than it looks. A Lean proof certifies that *a particular formal statement* follows from the axioms. Whether that statement is the theorem the paper claims is a separate, human question. OpenAI's repository documents, per paper, which checks cover a main theorem and which only a supporting result. Reading a formal statement and judging what it says is most of what this course teaches.

*Where the field stands.* Two pictures from public data. They compare Lean with [Rocq](https://rocq-prover.org/) (*Coq* until 2025) and [Isabelle/HOL](https://isabelle.in.tum.de/), the two other large proof assistants; how they differ is a question of foundations, taken up at the end of this chapter.

:::figure "New GitHub repositories per quarter, per million new repositories overall" (tag := "itp-repos")
![Line chart: new GitHub repositories per quarter for Lean, Coq/Rocq and Isabelle from 2018 to 2026, each per million new repositories overall; Lean rises from under ten to about two hundred while the others stay near ten](/static/figures/itp_github_repos_per_million.png)
:::

The counts are per million new repositories overall: absolute numbers mislead at the right-hand edge, because GitHub as a whole grew by 37 % in September 2026. One distortion is left in. The Justin Sun Prize, announced on 16 September 2026, pays up to a million dollars for a solved problem, but only against a machine-verified proof; 666 of that month's 3 224 new Lean repositories carry a prize identifier, and one account created 284 of them. Without the prize repositories and the near-empty ones, August to September is a factor of 1.5 rather than 2.

Until about 2023 the three were comparable, with Coq the largest. The rise is recent, and it is not evidence that Lean is better: Isabelle's automation is still ahead in places, and Rocq has decades of verified-software work behind it. It is evidence about where people are going.

:::figure "arXiv papers per week whose results are checked in Lean" (tag := "arxiv-lean")
![Bar chart: weekly count of arXiv papers with Lean-checked results during 2026, rising from about three per week in January to around forty per week in September](/static/figures/arxiv_lean_formalized_weekly.png)
:::

In January 2026 a handful of papers a week carried a machine-checked result; by September it was around forty. Within a few years, reading and writing a formal proof will be ordinary equipment.

*How it got here.* Four episodes over fifty years, each adding a different reason to want a machine to check mathematics. The idea is older than the tools. Gottlob Frege's *Begriffsschrift* of 1879 gave the first system in which proofs themselves were objects to be manipulated; Bertrand Russell's letter of 1902 showed that the system was inconsistent. Whitehead and Russell spent *Principia Mathematica* rebuilding; their proof that `1 + 1 = 2` arrives in the second volume with the note that *the above proposition is occasionally useful*. Done by hand, formalization is unbearable, and for most of a century little came of it. De Bruijn's *[Automath](https://en.wikipedia.org/wiki/Automath)* (1967) was the first system to check proofs mechanically, and in 1977 van Benthem Jutting pushed Landau's *Grundlagen der Analysis* through it -- the first complete mathematics book verified by machine.

In 1976 Kenneth Appel and Wolfgang Haken proved the [four colour theorem](https://en.wikipedia.org/wiki/Four_color_theorem). Their argument reduced the problem to a long list of configurations and then checked that list by computer. No human has ever read that part, and for two decades the community argued about whether it counted as a proof at all.

:::figure "Four colours suffice for any map in the plane. Georges Gonthier, who formalized the proof" (tag := "four-colour")
![A map of thirty-four regions, coloured with four colours so that no two neighbours share one](/static/figures/four_colour.png)

![Georges Gonthier (no photograph available)](/static/figures/portraits/placeholder_gonthier.png)
:::

In 2005 Georges Gonthier formalized the whole thing in Coq, case analysis included. The two events separate the distinction this course rests on: *a proof found by computer is not a proof checked by computer.*

In 1998 Thomas Hales announced a proof of the [Kepler conjecture](https://en.wikipedia.org/wiki/Kepler_conjecture): no packing of equal spheres in space is denser than the way a greengrocer stacks oranges.

:::figure "The packing Kepler conjectured to be optimal in 1611, and Thomas Hales, who proved it" (tag := "kepler")
![A pyramid of equal spheres, the face-centred cubic packing, with density pi over root 18](/static/figures/kepler_packing.png)

![Thomas Hales](/static/figures/portraits/hales.jpg)
:::

Twelve referees worked on it for four years and reported that they were ninety-nine percent certain, and could do no better. The *Annals of Mathematics* published it with that caveat. Hales started the [Flyspeck project](https://en.wikipedia.org/wiki/Flyspeck), which delivered a complete formal proof in HOL Light and Isabelle in 2014. This episode is not about computers: peer review had met a proof it could not certify, and more effort would not have helped.

In the third episode the author himself is the one in doubt. In 1989 Vladimir Voevodsky and Mikhail Kapranov published a theorem identifying [higher groupoids](https://en.wikipedia.org/wiki/Infinity-groupoid) with homotopy types. In October 1998 Carlos Simpson posted an argument implying that it could not be true. Voevodsky went on believing his own theorem until the autumn of 2013.

:::figure "Vladimir Voevodsky at Oberwolfach in 2011, during a workshop on the homotopy interpretation of type theory" (tag := "voevodsky")
![Vladimir Voevodsky](/static/figures/portraits/voevodsky.jpg)
:::

His account is about people, not machines. Simpson had a counterexample but could not say which step was wrong, so it stayed unclear who had erred. Mathematics runs, in Voevodsky's words, on *a complex system of mutual trust based on reputations*, and both authors had one. The doubt made the theorem unused without settling it, for fifteen years. A second mistake, in a lemma of his own from 1992, stood in print until a listener checking his lectures found it in 1999; several seminars had read the paper by then. A hard technical argument by a trusted author, he concluded, is *hardly ever checked in detail*.

Voevodsky received the Fields Medal in 2002. He then looked for a proof assistant he could use, found none that suited his mathematics, and built the foundations for one: [univalent foundations](https://en.wikipedia.org/wiki/Univalent_foundations), a special year at the Institute for Advanced Study in 2012-13, and the book two dozen people wrote there in under six months. He formalized in Coq, and his foundations are not the ones *Mathlib* rests on: Lean 2 carried a mode for them, Lean 3 dropped it. This course takes the diagnosis, not the cure. His [own account](https://www.ias.edu/ideas/2014/voevodsky-origins) is short. He died in 2017.

In December 2020 Peter Scholze posed a challenge on Kevin Buzzard's blog: a theorem in condensed mathematics whose proof he was not sure of. A Fields medallist, publicly unsure of his own argument, asking a machine to check it. The *[Liquid Tensor Experiment](https://leanprover-community.github.io/liquid/)*, led by Johan Commelin, finished in July 2022. *[Condensed mathematics](https://en.wikipedia.org/wiki/Condensed_mathematics)* rebuilds topology on profinite sets rather than on open covers.

:::figure "A profinite set: the Cantor set, built by removing middle thirds. Peter Scholze, who posed the challenge, and Johan Commelin, who led the project" (tag := "profinite")
![Seven stages of the middle-thirds construction, each row twice as many and three times as short as the one above](/static/figures/cantor_profinite.png)

![Peter Scholze](/static/figures/portraits/scholze.jpg)

![Johan Commelin (no photograph available)](/static/figures/portraits/placeholder_commelin.png)
:::
Buzzard's plenary lecture at the ICM in 2022 marks the point where formalization stopped being a curiosity.

:::figure "Leonardo de Moura, who started Lean in 2013" (tag := "demoura")
![Leonardo de Moura](/static/figures/portraits/demoura.jpg)
:::

Lean itself is recent. Leonardo de Moura started it at Microsoft Research in 2013. Lean 4, a redesign rather than a new version, arrived in 2021. Development now sits with the Lean FRO, a non-profit of roughly twenty people. Kevin Buzzard has argued for Lean among mathematicians since 2018.

*Landmark formalizations.* Between Flyspeck and 2026, each of these projects showed that something new was possible. The course material is built out of the libraries they left behind.

*[Perfectoid spaces](https://leanprover-community.github.io/lean-perfectoid-spaces/)*, 2019, by Buzzard, Commelin and Massot. They formalized a *definition* rather than a theorem: Scholze's [perfectoid spaces](https://en.wikipedia.org/wiki/Perfectoid_space) of 2012. Whether an object of that complexity could be stated at all in a proof assistant was open, and stating is a different problem from proving. Lean's reputation among mathematicians dates from this project. Perfectoid spaces are built over $`p`-adic fields:

:::figure "The 3-adic integers as an inverse limit. The three authors: Kevin Buzzard, Johan Commelin, Patrick Massot" (tag := "padic")
![A rooted ternary tree of depth four; the rows are labelled Z/3^0 up to Z/3^4, and each branch of the infinite tree is a 3-adic integer](/static/figures/padic_tree.png)

![Kevin Buzzard](/static/figures/portraits/buzzard.jpg)

![Johan Commelin (no photograph available)](/static/figures/portraits/placeholder_commelin.png)

![Patrick Massot (no photograph available)](/static/figures/portraits/placeholder_massot.png)
:::

*[Sphere eversion](https://leanprover-community.github.io/sphere-eversion/)*, 2022, by Massot, van Doorn and Nash: Gromov's [h-principle](https://en.wikipedia.org/wiki/Homotopy_principle), and with it the fact that a [sphere can be turned inside out](https://en.wikipedia.org/wiki/Sphere_eversion) without tearing or creasing. For closed curves in the plane no such thing is possible, and the reason is an invariant:

:::figure "Turning numbers of closed curves in the plane. The three authors: Patrick Massot, Floris van Doorn, Oliver Nash" (tag := "turning-number")
![Four closed plane curves with their turning numbers: a circle with 1, a figure eight with 0, a limacon with 2, and a three-looped curve with 3](/static/figures/turning_number.png)

![Patrick Massot (no photograph available)](/static/figures/portraits/placeholder_massot.png)

![Floris van Doorn (no photograph available)](/static/figures/portraits/placeholder_vandoorn.png)

![Oliver Nash (no photograph available)](/static/figures/portraits/placeholder_nash.png)
:::

A regular homotopy cannot change the turning number, and everting a circle would send $`+1` to $`-1`. In three dimensions the obstruction vanishes. Formalizing this meant differential topology rather than algebra, so the project built a usable differential-geometry API first and proved the theorem afterwards. That order is the ordinary shape of formalization work, and it is why *Mathlib* matters more than any single theorem in it.

*[The polynomial Freiman-Ruzsa conjecture](https://teorth.github.io/pfr/)*, 2023, by Gowers, Green, Manners and Tao, formalized under Tao's direction in about three weeks -- before the paper had been refereed. It says that a set whose sumset is barely larger than itself must be structured:

:::figure "A set of small doubling and its sumset. The four authors: Timothy Gowers, Ben Green, Terence Tao, Freddie Manners" (tag := "sumset")
![A set A of ten lattice points beside the set A+A of twenty-nine points, with the doubling constant 2.90](/static/figures/sumset.png)

![Timothy Gowers](/static/figures/portraits/gowers.jpg)

![Ben Green](/static/figures/portraits/green.jpg)

![Terence Tao](/static/figures/portraits/tao.jpg)

![Freddie Manners (no photograph available)](/static/figures/portraits/placeholder_manners.png)
:::

The method carried further than the theorem. A *blueprint* cuts a formalization into independent pieces with stated interfaces, so volunteers can work in parallel without talking to each other. Formalization stopped being a job for one team over years.

*[The Equational Theories Project](https://teorth.github.io/equational_theories/)*, 2024 to 2025, led by Tao: all 22 028 942 implications between 4 694 equational laws on magmas settled, with new constructions found on the way. The difficulty is not depth but bookkeeping, on a scale that needs a machine.

The laws are numbered. Equation 3 is $`x = x \diamond x`, Equation 4 is $`x = x \diamond y`. Proving an implication can be a single substitution; refuting one means building a magma.

```lean
abbrev Equation3 (a : Type) [Mul a] :=
  ∀ x : a, x = x * x

abbrev Equation4 (a : Type) [Mul a] :=
  ∀ x y : a, x = x * y

-- Equation 4 implies Equation 3: take y := x.
example (a : Type) [Mul a] (h : Equation4 a) :
    Equation3 a :=
  fun x => h x x

-- The converse fails: `and` on `Bool` is a
-- counterexample, and the machine checks it.
local instance : Mul Bool := ⟨(· && ·)⟩

example : Equation3 Bool := by decide
example : ¬ Equation4 Bool := by decide
```

That is one entry. The project settled 22 028 942 of them.

*[Sphere packing](https://en.wikipedia.org/wiki/Sphere_packing) in dimensions 8 and 24*. Viazovska proved the dimension-8 case in 2016 and received the Fields Medal for it. It belongs in the list above as much as here: the human project is the landmark, the five days in February 2026 are the news. The packing is the $`E_8` lattice, and its 240 shortest vectors carry the symmetry the proof uses:

:::figure "The 240 roots of the E8 lattice, projected onto the Coxeter plane. Maryna Viazovska, who proved the dimension-8 case" (tag := "e8")
![Two hundred and forty points arranged in eight concentric rings of thirty, joined by many short chords](/static/figures/e8_roots.png)

![Maryna Viazovska](/static/figures/portraits/viazovska.jpg)
:::

A human formalization project started in 2024 and was completed with an autoformalizer in February 2026, dimension 8 in five days. This closes the thread that opens with Kepler, four hundred years earlier.

*Other theorem provers.* The two systems Lean is usually compared with differ from it in their foundations, not in style.

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

*Lean and Rocq* are close relatives. Both rest on a dependent type theory in which a proof is a *term* and checking a proof is type-checking; both have an impredicative, proof-irrelevant universe `Prop` of propositions sitting under a predicative hierarchy of data types. Lean differs in four points that return later in these notes: proof irrelevance holds *definitionally*, quotient types are primitive rather than built from setoids, there is no universe cumulativity, and classical reasoning enters through an axiom (`Classical.choice`). Rocq's roots are in program verification -- the CompCert C compiler and the Feit-Thompson theorem are Rocq developments -- and it extracts verified programs to OCaml or Haskell.

*Isabelle/HOL* uses simple type theory: types are built from base types and arrows, types do not depend on terms, and one cannot write `Vec α n` for *lists of length `n`*. That logic is weak enough to automate well, and Isabelle's automation is the strongest of the three. *Sledgehammer* hands a goal to several external provers at once and reconstructs what they find as a proof Isabelle can check; much of what Lean's `grind` does, Isabelle has done for twenty years. Isabelle is also a framework: HOL is one object logic among several over the intuitionistic meta-logic Isabelle/Pure. Its largest development is *seL4*, an operating-system microkernel verified down to its C implementation.

*How the libraries are organized* matters more day to day than the foundations.

* *Mathlib* is one repository, compiled as a unit. Maintainers review every change, and CI keeps it building against the current Lean. There are no stable releases: *Mathlib* follows Lean, and your project follows *Mathlib*. Results combine without extra work, because all structures live in one hierarchy, built from `class` and `instance` (see the chapters on typeclasses and the algebraic hierarchy).
* *Rocq* has no such centre. Its standard library is small, and the mathematics lives in independent packages -- *MathComp*, out of the Feit-Thompson formalization, *Coquelicot* and *MathComp-Analysis* for analysis, and others -- distributed through `opam`, with the *Rocq Platform* bundling a tested combination. Packages evolve at their own pace, which is comfortable with one dependency and awkward with two that disagree.
* *Isabelle* sits in between. The *Archive of Formal Proofs* holds refereed, self-contained entries, released in lockstep with Isabelle. Entries may depend on one another but are never merged into one library; the archive is cited like a journal.

We use Lean because *Mathlib* exists: the exercises start with `import Mathlib` and have the real numbers, measure theory and topology already there.

*Other courses.*

* [_Natural Number Game_](https://adam.math.hhu.de/#/g/leanprover-community/nng4): proofs about `ℕ` in the browser, nothing to install. The usual first contact with Lean, and a good use of an evening before the course starts.
* [_Formalising Mathematics_](https://b-mehta.github.io/formalising-mathematics-notes/) by Bhavik Mehta, after notes by Kevin Buzzard: the format of the present course follows these.
* [_Mathematics in Lean_](https://leanprover-community.github.io/mathematics_in_lean/) by Jeremy Avigad and Patrick Massot: the closest thing to an official course, organized by area of mathematics.

*Some notes on Lean and Mathlib.*

* Lean is also a programming language; see [Functional Programming in Lean](https://lean-lang.org/functional_programming_in_lean/).
* [*Mathlib*](https://github.com/leanprover-community/mathlib4) is a library written in Lean, collecting mathematical results. Every file in this course starts with `import Mathlib`, so we make no distinction between the two.
* Measured on the version pinned for this course (15 September 2026): 8 529 files, 2.33 million lines, about 189 000 theorems and lemmas, about 64 000 definitions, instances and structures, by 1 031 contributors in 34 768 commits. In the thirty days before that date it received 820 commits, 27 per day. The library changes while you use it.
* The [interactive import map](https://leanprover-community.github.io/mathlib4_docs/mathlib.html) draws *Mathlib* as a graph of its modules; the same site serves the [API documentation](https://leanprover-community.github.io/mathlib4_docs/) for every declaration. Both are worth half an hour before you need them.

*Practical matters.* The rest of this chapter is about running the course.

*Goals.* The course is for mathematics students.

* *Interactive theorem proving.* A small kernel checks every logical step of a proof, and the editor reports what remains to be proved as you write. This is not the older use of computers in mathematics, which was to work through many cases.
* *Mathematical content.* The mathematics in the first half is deliberately easy, because explaining a proof to a computer requires understanding it first, and a proof of more than a few lines has to be planned so that the commands -- *tactics* -- fit together. The second half goes deeper into the mathematics.
* *Functional programming.* Inductive types, structures, typeclasses and monads, needed both to use Lean and to read *Mathlib*. These are spread across the Lean and Mathematics parts rather than collected in one chapter.
* *Type theory.* Lean rests on dependent type theory: the Curry-Howard correspondence, dependent types, the universe hierarchy, and Lean's axioms.
* *Mathematics in Mathlib.* How the library organizes order theory, the algebraic hierarchy, filters (a single framework for limits), topology, measure theory and discrete probability. Textbooks rarely treat these from the point of view of formalization.
* *Proof engineering.* Automation tactics, searching *Mathlib*, and the common pitfalls of a large formal library.

*How the course is organized.* Tactics and theory are interleaved rather than separated.

* The first part, *Lean and its type theory*, introduces writing proofs and the dependent type theory underneath at the same time.
* Tactics are documented alphabetically in a glossary in the *Appendix*. You will usually meet a tactic in a working example before reading its entry; a table at the start of *Proofs in Lean* lists the ones needed first.
* Read in order, but on a first pass you can skip the tactics chapter and consult it when you hit a `sorry`.

*How to use this course.* The notes have five parts.

* *Lean and its type theory*: first the language, writing proofs, the functional-programming side (pure functions, pattern matching, recursion, higher-order functions) and navigating *Mathlib*; then the theory -- Curry-Howard, dependent types, universes, Lean's three axioms and what the kernel adds to them, the `structure` / `class` machinery, well-foundedness and the avoidance of paradoxes.
* *Mathematics*: propositions, proofs and sets, then how *Mathlib* organizes order theory, the algebraic hierarchy, filters, topology, measure theory and monadic discrete probability (`PMF`). Pointers into the API, not full formalizations.
* *Appendix*: common pitfalls, the diagnostic commands (`#print axioms`, `#find_home`, `#lint`), a keyword reference and the glossary of tactics (a longer list is [here](https://github.com/haruhisa-enomoto/mathlib4-all-tactics/blob/main/all-tactics.md)).
* *Projects*: five topics for the individual formalization projects in the second half, each with a description, a sketch of an implementation and references.
* *Bibliography*: the works cited throughout, with links.

*Slides.* Some chapters have a deck, used in the lecture and readable on its own. The figures and claims are those of the text, so either can be used without the other.

* [Why formalize?](slides/introduction/) -- the first lecture: what formalizing means, where things stand in 2026, the four episodes and the landmark formalizations.
* [Filters in Mathlib](slides/filters/) -- accompanies the chapter on filters.

Press `s` in a deck for the speaker notes, `o` for an overview of all slides, and `?` for the remaining keys.

The exercises carry the course (the _Exercises_ folder within `Leancourse`). Feedback is immediate: error messages from the elaborator, and a *proof-state* panel showing what remains to be proved at every cursor position. Start with the first sheet; the sheets explain as they go.

The sheets cover the first half of the semester. In the second half you work on an individual project, mostly self-chosen -- an exercise from your first year, or a part of `Mathlib` you want to know; the {ref "projects"}[Projects chapter] has five worked-out suggestions.

Before the first exercise session, get Lean running on your own machine.

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

Measured on the version of *Mathlib* used here: compiling one sheet peaks at about 6.6 GB of resident memory, and the language server behind *vscode* sits at roughly 9 GB with one file open. Most of that is memory-mapped library data, which the system can drop and read back from disk, so less memory does not break anything, it only slows everything down. With 8 GB you can work with a single file open and little else running. On a mechanical hard disk you cannot.

*If your machine is below the minimum, talk to the teachers at the start of the course.* A server with 128 GB of RAM is available and we can give you an account on it.

Run the `git clone` and `lake exe cache get` below at home, before the first lab session: `lake exe cache get` downloads several gigabytes, and twenty people doing that at once on one network is slow for all of them.

* Installation of [vscode](https://code.visualstudio.com/).
* Open `vscode`, hit the _extensions_ icon (fifth from the top) on the left, and install the _Lean 4 language extension_.
* Install `git`, if you do not have it: open `vscode`, hit the _git_ icon (third from the top on the left), and follow the instructions.
* The exercises repository. Go to where you want the course materials and run
```
git clone https://github.com/pfaffelh/leancourse_exercises
cd leancourse_exercises
lake exe cache get
code .
```
_vscode_ opens with the course materials. (These notes are generated from a second repository, [pfaffelh/leancourse](https://github.com/pfaffelh/leancourse), which you do not need to clone.)

:::paragraph
Another description of the installation is [here](https://leanprover-community.github.io/get_started.html#regular-install).
:::


After `code .` in the `leancourse_exercises` folder, open `Exercises/01-Logic/01-a-Propositions.lean`. It works once the orange and red bars disappear and moving the cursor on the left changes the infoview on the right.
* Copy the `Exercises` directory to `MyExercises` and work there. `MyExercises` is ignored by git, so an update never overwrites your files.
* To update, run `git pull` in `leancourse_exercises`.

If the installation gives you trouble, talk to the teachers rather than spending evenings on it.

*Picture credits.* The mathematical figures were generated by the scripts in `scripts/figures/` and may be reused freely. The photographs come from Wikimedia Commons and are reproduced unchanged under their own licences:

* Thomas Hales -- Slawekb, CC BY-SA 3.0, [via Wikimedia Commons](https://commons.wikimedia.org/wiki/File:Halescropped.jpg)
* Peter Scholze -- George Bergman, CC BY-SA 4.0, [via Wikimedia Commons](https://commons.wikimedia.org/wiki/File:Peter_Scholze_2014_cropped.jpg)
* Kevin Buzzard -- George Bergman, CC BY-SA 4.0, [via Wikimedia Commons](https://commons.wikimedia.org/wiki/File:Kevin_Buzzard_1996_(headshot).jpg)
* Leonardo de Moura -- David Monniaux, CC BY-SA 4.0, [via Wikimedia Commons](https://commons.wikimedia.org/wiki/File:Leo_de_Moura_P1210629.jpg)
* Maryna Viazovska -- Petra Lein, Archives of the Mathematisches Forschungsinstitut Oberwolfach, CC BY-SA 2.0 de, [via Wikimedia Commons](https://commons.wikimedia.org/wiki/File:Maryna_Vazovska_MFO_2013_crop.jpg)
* Timothy Gowers -- Gert-Martin Greuel, Archives of the Mathematisches Forschungsinstitut Oberwolfach, CC BY-SA 2.0 de, [via Wikimedia Commons](https://commons.wikimedia.org/wiki/File:William_Timothy_Gowers_Oslo_2012.jpg)
* Ben Green -- Renate Schmid, Archives of the Mathematisches Forschungsinstitut Oberwolfach, CC BY-SA 2.0 de, [via Wikimedia Commons](https://commons.wikimedia.org/wiki/File:Ben_Green.jpg)
* Vladimir Voevodsky -- Renate Schmid, Archives of the Mathematisches Forschungsinstitut Oberwolfach, CC BY-SA 2.0 de, [via Wikimedia Commons](https://commons.wikimedia.org/wiki/File:VladimirVoevodsky.jpg)
* Terence Tao -- Institute for Pure and Applied Mathematics, CC BY 4.0, [via Wikimedia Commons](https://commons.wikimedia.org/wiki/File:Terence_Tao_at_IPAM%27s_Fireside_Chat_2026_%2850m16s%29_%28cropped%29.jpg)

The two product marks in this chapter -- Claude and ChatGPT -- are also from Wikimedia Commons, under CC0 and in the public domain respectively. They remain trademarks of their owners and are used here only to say which system produced which proof.

Several people who appear in this chapter have no freely licensed photograph, and the pattern is not an accident: Georges Gonthier, who formalized both the four colour theorem and the [Feit-Thompson theorem](https://en.wikipedia.org/wiki/Feit%E2%80%93Thompson_theorem), Johan Commelin, who led the Liquid Tensor Experiment, Patrick Massot, Floris van Doorn and Oliver Nash, who formalized sphere eversion, and Freddie Manners, one of the four authors of the polynomial Freiman-Ruzsa theorem. They appear above as grey silhouettes with their initials. The photographs are therefore a fair sample of who is *famous*, not of who did this work, and the silhouettes are left visible rather than quietly omitted for that reason.

{include 0 «Leancourse».Coursenotes.«01-Lean»}

{include 0 «Leancourse».Coursenotes.«03-Mathematics»}

{include 0 «Leancourse».Coursenotes.«04-Appendix»}

{include 0 «Leancourse».Coursenotes.«05-Projects»}

{include 0 «Leancourse».Coursenotes.«99-Bibliography»}
