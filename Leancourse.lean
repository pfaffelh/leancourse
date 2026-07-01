-- This module serves as the root of the `Leancourse` library.
-- Import modules here that should be built as part of the library.
import VersoManual
import Mathlib

import «Leancourse».Coursenotes.«01-Lean»
import «Leancourse».Coursenotes.«03-Mathematics»
import «Leancourse».Coursenotes.«04-Appendix»
import «Leancourse».Coursenotes.«99-Bibliography»

open Verso.Genre Manual

#doc (Manual) "Interactive Theorem Proving using Lean, Winter 2026/27" =>
%%%
tag := "ITPFr"
authors := ["Peter Pfaffelhuber"]
%%%

These are the notes for a course on formal proving with the interactive theorem prover Lean4 (in the following we just write Lean) in the winter semester of 2026/27 at the University of Freiburg. To be able to work through the course in a meaningful way, the following technical preparations are to be made:

* Installation of [vscode](https://code.visualstudio.com/).
* Open `vscode`, hit the _extensions_ icon (fifth from the top) on the left, and install the _Lean 4 language extension_.
* If you haven't done already, install `git`. For this, the best way is to open `vscode`, hit the _git_ icon (third from the top on the left), and follow the instructions.
* Installing the course repository: Navigate to a location where you would like to put the course materials and use
```
git clone https://github.com/pfaffelh/leancourse
cd leancourse
lake exe cache get
code .
```
Then, _vscode_ should open and you see the course materials.

:::paragraph
Note: Yet another description how to install _Lean_ is found [here](https://leanprover-community.github.io/get_started.html#regular-install).
:::


After having typed `code .` within the `leancourse` folder, navigate to `Leancourse/Exercises/01-Logic/01-a.lean`. Everything is fine once orange and/or red bars disapprear, and navigating in the left hand side of the windom leads to changes in the right hand side (the infoview). You should see some code which looks a bit like mathematics.
* The directory `Leancourse/Exercises` contains the material for the course. We recommend that you first copy this directory, for example to `myExercises`. Otherwise, an update of the repository may overwrite the local files.
* To update the course materials, enter `git pull` from within the `leancourse`directory.

In case you cannot install the course material locally, do the following: Visit [this page](https://github.com/pfaffelh/leancourse) and click on the green Code-button. Navigate to Codespaces and open the course notes there. You get a window which looks a lot like _vscode_, so please follow the instructions from above. You will have to _Restart Lean_ and _Restart File_ and wait several minutes until all is set. (If you see a red vertical bar, something is wrong. If you see an orange vertical bar, you will have to wait longer.) You will probably need a github account in order to open the coursenotes in Codespaces.

:::paragraph
For the very first exercise sheets you do not even need a local installation: you can run Lean 4 directly in your browser. Two web editors that give you Lean 4 together with _Mathlib_ are [live.lean-lang.org](https://live.lean-lang.org/) (the official Lean 4 playground) and the instance at [lean.math.hhu.de](https://lean.math.hhu.de/) hosted by HHU Düsseldorf. Paste an exercise in, make sure the file starts with `import Mathlib`, and wait a moment for Lean to start up. This is the quickest way to get going; for the full course -- many files, faster feedback, and saving your own work -- a local setup or Codespaces is preferable.
:::

*Goals.* The course is designed for mathematics students and has several goals:

* Learning the techniques for interactive theorem proofing using Lean: In recent years, efforts to prove mathematical theorems with the help of computers have increased dramatically. While a few decades ago, it was more a matter of consistently processing many cases that were left to the computer, interactive theorem provers are different. Here, a very small core can be used to understand or interactively generate all the logical conclusions of a mathematical proof. The computer then reports interactively on the progress of the proof and when all the steps have been completed.
* Establishing connections to some mathematical material: At least in the first half, the mathematical details needed in this course should not be the main issue of this course. However, in order to _explain_ how a proof (or calculation or other argument) to a computer, you first have to understand it very well yourself. Furthermore, you have to plan the proof well - at least if it exceeds a few lines - so that the commands you enter (which we will call tactics) fit together. The course intends to teach both, first steps in `Lean` and learning a bunch of these tactics, and make a deeper dive into some mathematical material.
* Understanding functional programming: Lean is not only a theorem prover but also a functional programming language. We cover core concepts such as inductive types, structures, typeclasses, and monads, which are essential both for using Lean effectively and for understanding how Mathlib is organized. These topics are distributed across the Lean and Mathematics parts of the notes rather than collected into a chapter of their own.
* Learning type theory: The foundation of Lean is dependent type theory. We explore the Curry-Howard correspondence, dependent types, the universe hierarchy, and the axioms underlying Lean, providing the theoretical background for why interactive theorem proving works.
* Exploring advanced mathematics in Lean: We survey how Mathlib organizes order theory, the algebraic hierarchy, filters (which provide a unified framework for limits), topology, measure theory, and discrete probability. These topics are not always well covered in standard textbooks from the perspective of formalization.
* Proof engineering: We learn to use powerful automation tactics, navigate Mathlib effectively, and avoid common pitfalls when working with a large formal library.

*Other material and theorem provers.* Lean is not the only theorem prover, and, of course, this course is not the only course trying to teach Lean to you. Other Theorem provers (which all will be neglected here) are:

* [Rocq](https://rocq-prover.org/) (formerly COQ)
* [Isabelle/HOL ](https://isabelle.in.tum.de/)

Other courses, which you might want to have a look at are:

* [_Natural Number Game_](https://adam.math.hhu.de/#/g/leanprover-community/nng4): In case you are reading this text in advance and have some spare time, it is highly recommended to start this (online) game, making you prove first things on `ℕ` using Lean. It is a classical way to start your first contact with Lean.
* [_Formalising Mathematics_](https://b-mehta.github.io/formalising-mathematics-notes/) by Bhavik Mehta, based on notes by Kevin Buzzard: these notes have inspired at least the format of the present course.
* [_Mathematics in Lean_](https://leanprover-community.github.io/mathematics_in_lean/) by Jeremy Avigad and Patrick Massot: if there is something like an official course maintained by experts in charge, this is probably it. It is mainly concentrated about different areas of mathematics.

*Some notes on Lean and Mathlib.*

* Hardware requirements: running Lean locally is comfortable with roughly 8 GB of RAM or more. If your machine is smaller, you can still follow the course: use a cloud-based setup such as Gitpod or the Lean web editor linked from the [Lean community page](https://leanprover-community.github.io/). With that in mind, here is what you will need to follow along.
* Lean is not only an interactive theorem prover, but also a programming language. If you want to know/learn more about this aspect, please consult [Functional programming in Lean](https://lean-lang.org/functional_programming_in_lean/).
* While `Lean` is a programming language, `Mathlib` is a library in the Lean language. It collects various (more or less deep) mathematical results. In this course, we do not make any distinction between `Lean` and `Mathlib`, since we will have `import Mathlib` at the start of any file we will need results from there. In this way, we have access to a large part of mathematics in order to solve exercises.

*How the course is organized.* Unlike a textbook, this course interleaves tactics and theory rather than separating them. Concretely:

* The first part, *Lean and its type theory*, introduces both tactical reasoning (writing proofs) and the dependent type theory that underlies it.
* Tactics are documented *alphabetically* in their own chapter. That chapter is a glossary, not a narrative. You will often meet a tactic in a working example before you read its entry; a preview table at the start of *Proofs in Lean* lists the ones you will need first.
* We recommend reading in order, but on a first pass it is fine to skip the tactics chapter and consult it when you hit a `sorry` proof.

*How to use this course.* These notes are organized into the following parts, followed by a reference appendix and a bibliography:

* *Lean and its type theory*: Lean both as a proof assistant and as a dependent type theory. We start hands-on -- the language, writing proofs, the functional-programming side of Lean (pure functions, pattern matching, recursion, higher-order functions), navigating Mathlib, and an *alphabetical reference* for the main tactics (a preview table appears at the start of *Proofs in Lean*; an even longer list lives [here](https://github.com/haruhisa-enomoto/mathlib4-all-tactics/blob/main/all-tactics.md)). We then turn to the theory: the Curry-Howard correspondence, dependent types, universes, the three axioms of Lean (and what the kernel additionally bakes in), the `structure` / `class` machinery that underpins Mathlib, and well-foundedness and the avoidance of paradoxes.
* *Mathematics*: after an opening chapter on the everyday foundations -- propositions, proofs, and sets -- we survey how Mathlib organizes order theory, the algebraic hierarchy, filters, topology, measure theory, and monadic discrete probability (`PMF`), with pointers into the relevant Mathlib API rather than full formalizations.
* *Appendix*: common pitfalls when working with Lean and Mathlib, the diagnostic commands (`#print axioms`, `#find_home`, `#lint`), and an alphabetical keyword reference.
* *Bibliography*: the works cited throughout, with links.

The heart of the course are the exercises (see the _Exercises_ folder within `Leancourse`). Unlike in other courses, you will get immediate feedback on any single exercise -- via error messages from the elaborator and a live *proof-state* panel that shows what remains to be proved at every cursor position. If you want to start right away, please start immediately with the first exercise sheet. More explanations will be given within the exercise sheets.

While the exercises will cover the first half of the semester, individual assignments will happen in the latter part of this course. (These will mostly be self-assigned, so e.g. you will formalize an exercise from your first year of studies, or you are interested in a specific part of `Mathlib`, or...)

# Table of Contents

{include 0 «Leancourse».Coursenotes.«01-Lean»}

{include 0 «Leancourse».Coursenotes.«03-Mathematics»}

{include 0 «Leancourse».Coursenotes.«04-Appendix»}

{include 0 «Leancourse».Coursenotes.«99-Bibliography»}
