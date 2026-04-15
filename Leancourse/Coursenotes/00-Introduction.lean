import VersoManual

open Verso.Genre Manual

set_option pp.rawOnError true

#doc (Manual) "Introduction" =>
%%%
htmlSplit := .never
tag := "introduction"
%%%

# Goals
%%%
tag := "goals"
%%%

The course is designed for mathematics students and has several goals:

* Learning the techniques for interactive theorem proofing using Lean: In recent years, efforts to prove mathematical theorems with the help of computers have increased dramatically. While a few decades ago, it was more a matter of consistently processing many cases that were left to the computer, interactive theorem provers are different. Here, a very small core can be used to understand or interactively generate all the logical conclusions of a mathematical proof. The computer then reports interactively on the progress of the proof and when all the steps have been completed.
* Establishing connections to some mathematical material: At least in the first half, the mathematical details needed in this course should not be the main issue of this course. However, in order to _explain_ how a proof (or calculation or other argument) to a computer, you first have to understand it very well yourself. Furthermore, you have to plan the proof well - at least if it exceeds a few lines - so that the commands you enter (which we will call tactics) fit together. The course intends to teach both, first steps in `Lean` and learning a bunch of these tactics, and make a deeper dive into some mathematical material.
* Understanding functional programming: Lean is not only a theorem prover but also a functional programming language. We cover core concepts such as inductive types, structures, typeclasses, and monads, which are essential both for using Lean effectively and for understanding how Mathlib is organized. These topics are distributed across the Lean basics, Type Theory, and Advanced Mathematics parts of the notes rather than collected into a chapter of their own.
* Learning type theory: The foundation of Lean is dependent type theory. We explore the Curry-Howard correspondence, dependent types, the universe hierarchy, and the axioms underlying Lean, providing the theoretical background for why interactive theorem proving works.
* Exploring advanced mathematics in Lean: We survey how Mathlib organizes order theory, the algebraic hierarchy, filters (which provide a unified framework for limits), topology, measure theory, and discrete probability. These topics are not always well covered in standard textbooks from the perspective of formalization.
* Proof engineering: We learn to use powerful automation tactics, navigate Mathlib effectively, and avoid common pitfalls when working with a large formal library.

# Other material and Theorem provers
%%%
tag := "other-theorem-provers"
%%%

Lean is not the only theorem prover, and, of course, this course is not the only course trying to teach Lean to you. Other Theorem provers (which all will be neglected here) are:

* [Rocq](https://rocq-prover.org/) (formerly COQ)
* [Isabelle/HOL ](https://isabelle.in.tum.de/)

Other courses, which you might want to have a look at are:

* [_Natural Number Game_](https://adam.math.hhu.de/#/g/leanprover-community/nng4): In case you are reading this text in advance and have some spare time, it is highly recommended to start this (online) game, making you prove first things on `ℕ` using Lean. It is a classical way to start your first contact with Lean.
* [_Formalizing Mathematics 2025_](https://b-mehta.github.io/formalising-mathematics-notes/) by Bhavik Mehta, based on notes by Kevin Buzzard: these notes have inspired at least the format of the present course.
* [_Mathematics in Lean_](https://leanprover-community.github.io/mathematics_in_lean/) by Jeremy Avigad and Patrick Massot: if there is something like an official course maintained by experts in charge, this is probably it. It is mainly concentrated about different areas of mathematics.

# Some notes on Lean and Mathlib
%%%
tag := "some-notes"
%%%

* Hardware requirements: running Lean locally is comfortable with roughly 8 GB of RAM or more. If your machine is smaller, you can still follow the course: use a cloud-based setup such as Gitpod or the Lean web editor linked from the [Lean community page](https://leanprover-community.github.io/). With that in mind, here is what you will need to follow along.
* Lean is not only an interactive theorem prover, but also a programming language. If you want to know/learn more about this aspect, please consult [Functional programming in Lean](https://lean-lang.org/functional_programming_in_lean/).
* While `Lean` is a programming language, `Mathlib` is a library in the Lean language. It collects various (more or less deep) mathematical results. In this course, we do not make any distinction between `Lean` and `Mathlib`, since we will have `import Mathlib` at the start of any file we will need results from there. In this way, we have access to a large part of mathematics in order to solve exercises.

# How the course is organized
%%%
tag := "structure"
%%%

Unlike a textbook, this course interleaves tactics and theory rather than separating them. Concretely:

* Chapters 01 and 02 introduce both tactical reasoning (writing proofs) and the type theory that underlies it.
* Tactics are documented *alphabetically* in their own chapter. That chapter is a glossary, not a narrative. You will often meet a tactic in a working example before you read its entry; a preview table at the start of *Proofs in Lean* lists the ones you will need first.
* We recommend reading in order (00 → 04), but on a first pass it is fine to skip the tactics chapter and consult it when you hit a `sorry` proof.

# How to use this course
%%%
tag := "howto"
%%%

These notes have five main parts (numbered 0--4, matching the
directory layout):

* *Introduction* (Chapter 0): the document you are currently reading.
* *Lean* (Chapter 1): general hints on Lean as a language and as a proof assistant. We cover background on dependent type theory, the functional-programming side of Lean (pure functions, pattern matching, recursion, higher-order functions), and an *alphabetical reference* for the main tactics you will use to write proofs interactively. The tactics chapter is meant as a glossary: you will encounter the most important tactics in the narrative first (a short preview table appears at the start of *Proofs in Lean*), and look up individual entries as needed. An even longer list lives [here](https://github.com/haruhisa-enomoto/mathlib4-all-tactics/blob/main/all-tactics.md).
* *Type Theory* (Chapter 2): the theoretical foundation of Lean. We explore the Curry-Howard correspondence, dependent types, universes, the axioms of Lean's type theory, and the `structure` / `class` machinery that underpins Mathlib.
* *Advanced Mathematics* (Chapter 3): we survey how Mathlib organizes more advanced mathematical topics -- order theory, the algebraic hierarchy, filters, topology, measure theory, and monadic discrete probability (`PMF`) -- with pointers into the relevant Mathlib API rather than full formalizations.
* *Advanced Topics* (Chapter 4): practical skills for working with Lean and Mathlib at scale: automation tactics, navigating the library, and avoiding common pitfalls.

The heart of the course are the exercises (see the _Exercises_ folder within `Leancourse`). Unlike in other courses, you will get immediate feedback on any single exercise -- via error messages from the elaborator and a live *proof-state* panel that shows what remains to be proved at every cursor position. If you want to start right away, please start immediately with the first exercise sheet. More explanations will be given within the exercise sheets.

While the exercises will cover the first half of the semester, individual assignments will happen in the latter part of this course. (These will mostly be self-assigned, so e.g. you will formalize an exercise from your first year of studies, or you are interested in a specific part of `Mathlib`, or...)
