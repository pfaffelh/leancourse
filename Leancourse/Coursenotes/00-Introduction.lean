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
* Understanding functional programming: Lean is not only a theorem prover but also a functional programming language. We cover core concepts such as inductive types, structures, typeclasses, and monads, which are essential both for using Lean effectively and for understanding how Mathlib is organized.
* Learning type theory: The foundation of Lean is dependent type theory. We explore the Curry-Howard correspondence, dependent types, the universe hierarchy, and the axioms underlying Lean, providing the theoretical background for why interactive theorem proving works.
* Exploring advanced mathematics in Lean: We cover topics such as order theory, the algebraic hierarchy in Mathlib, filters (which provide a unified framework for limits), topology, and measure theory. These topics are not always well covered in standard textbooks from the perspective of formalization.
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

* Hardware requirements: In fact, Lean will require a decent hardware, e.g. at least 8GB of RAM in order to function properly. If you do not have this, there are ways of using Lean online; see above.
* Lean is not only an interactive theorem prover, but also a programming language. If you want to know/learn more about this aspect, please consult [Functional programming in Lean](https://lean-lang.org/functional_programming_in_lean/).
* While `Lean` is a programming language, `Mathlib` is a library in the Lean language. It collects various (more or less deep) mathematical results. In this course, we do not make any distinction between `Lean` and `Mathlib`, since we will have `import Mathlib` at the start of any file we will need results from there. In this way, we have access to a large part of mathematics in order to solve exercises.

# How to use this course
%%%
tag := "howto"
%%%

These notes have seven main parts:

* **Introduction and Lean basics** (Chapters 1-2): Starting in the next chapter, we give general hints on Lean, which are rather for reference and background than for starting the course. You will almost certainly find yourself asking fundamental things on Lean (e.g. _What is type theory, and why should I care?_), which we try to explain without too much detail. We also introduce basic mathematical objects in Lean: logical claims, `ℕ`, `ℝ`, sets and functions.
* **Tactics** (Chapter 3): When interactively writing proofs, a main focus will be the currently _proof state_. In order to modify it, we need tactics, which in some sense feels like learning a new language (which is in fact true). We give an overview of the most important tactics. A more comprehensive overview is [here](https://github.com/haruhisa-enomoto/mathlib4-all-tactics/blob/main/all-tactics.md).
* **Projects** (Chapter 4): Student projects from previous iterations of this course, demonstrating what can be achieved.
* **Functional Programming** (Chapter 5): Lean is a functional programming language. We cover recursion, pattern matching, structures, typeclasses, and monads - the building blocks that make both Lean programs and Mathlib work.
* **Type Theory** (Chapter 6): The theoretical foundation of Lean. We explore the Curry-Howard correspondence, dependent types, universes, and the axioms of Lean's type theory.
* **Advanced Mathematics** (Chapter 7): We formalize more advanced mathematical topics: order theory, the algebraic hierarchy, filters, topology, and measure theory.
* **Proof Engineering** (Chapter 8): Practical skills for working with Lean and Mathlib at scale: automation tactics, navigating the library, and avoiding common pitfalls.

The heart of the course are the exercises (see the _Exercises_ folder within `Leancourse`). Unlike in other courses, you will get immediate feedback of how well you performed on any single exercise. If you want to start right away, please start immediately with the first exercise sheet. More explanations will be given within the exercise sheets.

While the exercises will cover the first half of the semester, individual assignments will happen in the latter part of this course. (These will mostly be self-assigned, so e.g. you will formalize an exercise from your first year of studies, or you are interested in a specific part of `Mathlib`, or...)
